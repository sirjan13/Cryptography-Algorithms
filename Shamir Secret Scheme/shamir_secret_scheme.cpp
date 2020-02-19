#include <bits/stdc++.h>

typedef unsigned char byte;

#define MAX_VALUE 255

using namespace std;


vector<byte> n_random_bytes(int n, int min_value, int max_value) {
    random_device device;
    mt19937 generator(device());
    uniform_int_distribution<int> distribution(min_value, max_value);
    vector<byte> random_bytes;
    for(int byte_i = 1; byte_i <= n; byte_i++) {
        random_bytes.push_back(distribution(generator));
    }
    return random_bytes;
}



class galois_256_field {
    private:
    public:
        byte LOG[256];
        byte EXP[256];
        byte mul[256][256];
        byte DIV[256][256];


        galois_256_field() {

        }

        byte add(byte a, byte b) {
            return (byte) (a ^ b);
        }

        byte subtract(byte a, byte b) {
            return add(a, b);
        }

        byte multiply_1(byte a, byte b) {
            byte counter = a;
            byte value = b;
            byte product = 0;
            while(counter) {
                if(counter & 1) {
                    product = (byte) (product ^ value);
                }
                byte term = (byte) (value & 128);
                value = (byte) (value << 1);
                if(term)
                    value = (byte) (value ^ 0x1b);
                counter = (byte) ((counter & 0xff) >> 1);
            }
            return product;
        }

        byte multiply_2(byte a, byte b) {
            if(!a or !b)
                return 0;
            int term = (LOG[a & 0xff] & 0xff) + (LOG[b & 0xff] & 0xff);
            if(term > MAX_VALUE)
                term -= MAX_VALUE;
            return EXP[term & 0xff];
        }

        byte _divide(byte a, byte b) {
            if(!a or !b)
                return 0;
            int term = (LOG[a & 0xff] & 0xff) - (LOG[b & 0xff] & 0xff);
            if(term < 0)
                term += MAX_VALUE;
            return EXP[term & 0xff];
        }


        void init() {
            byte x = 1;
            EXP[0] = x;
            
            byte generator = 0x03;
            for(int i = 1; i <= MAX_VALUE; i++) {
                byte y = multiply_1(x, generator);
                EXP[i] = y;
                x = y;
            }

            for(int i = 0; i <= MAX_VALUE; i++) {
                LOG[EXP[i] & 0xff] = (byte) i;
            }
            
            for(int i = 0; i <= MAX_VALUE; i++) {
                for(int j = 0; j <= MAX_VALUE; j++) {
                    mul[i][j] = multiply_2((byte)(i & 0xff), (byte)(j & 0xff));
                    DIV[i][j] = _divide((byte)(i & 0xff), (byte)(j & 0xff));
                }
            }
        }

        byte multiply(byte a, byte b) {
            if(a == 0 || b == 0) {
              return 0;
            }
            return mul[a & 0xff][b & 0xff];
        }

        byte divide(byte a, byte b) {
            return DIV[a & 0xff][b & 0xff];
        }
};


class polynomial {

    public:

        galois_256_field g256;
        vector<byte> coeff;
        
        polynomial() {
            g256.init();
            coeff.clear();
        }

        int get_degree(vector<byte> coefficients) {
            int degree = 0;
            for(int i = coefficients.size() - 1; i >= 0; i--) {
                if(coefficients[i]) {
                    degree = i;
                    break;
                }
            }
            return degree;
        }

        polynomial(byte secret, int target_degree) {
            vector<byte> polynomial_coeff;
            while(1) {
                polynomial_coeff = n_random_bytes(target_degree + 1, 0, 255);
                int curr_degree = get_degree(polynomial_coeff);
                if(curr_degree == target_degree) {
                    polynomial_coeff[0] = secret;
                    break;
                }
            }
            coeff = polynomial_coeff;
        }

        // Find f(X) given coefficients of the Polynomial
        byte evaluate(byte X) {
            byte Y = 0;
            for(int i = coeff.size() - 1; i >= 0; i--) {
                Y = g256.add(g256.multiply(X, Y), coeff[i]);
            }   
            return Y;
        }
};


class shamir_secret {
    public:

        string secret;
        galois_256_field g256; 
        vector<byte> bytes;
        vector<vector<byte>> shards;
        int n_shards;
        int k;
        
        shamir_secret(string s, int parts, int min_req) {
        	g256.init();
            secret = s;
            bytes = vector<byte> (secret.begin(), secret.end());
            n_shards = parts;
            k = min_req;
            shards.assign(n_shards + 1, vector<byte> (secret.size(), 0));
            for(int byte_i = 0; byte_i < secret.size(); byte_i++) {
                byte ith_secret = secret[byte_i];
                polynomial ith_polynomial(ith_secret, k - 1);
                for(int shard_id = 1; shard_id <= n_shards; shard_id++) {
                    shards[shard_id][byte_i] = ith_polynomial.evaluate((byte) shard_id);
                }
            }
        } 


        byte lagrange_evaluate(vector<pair<byte, byte>> shard_points) {
            byte X = 0, Y = 0;
            int n = shard_points.size();
            for(int i = 0; i < n; i++) {
                byte prod_li = 1;
                byte x0 = shard_points[i].first;
                for(int j = 0; j < n; j++) {
                    if(i == j) continue;
                    byte x1 = shard_points[j].first;
                    byte numerator = g256.subtract(X, x1);
                    byte denominator = g256.subtract(x0, x1);
                    byte li = g256.divide(numerator, denominator);
                    prod_li = g256.multiply(prod_li, li);
                }
                byte y0 = shard_points[i].second;
                Y = g256.add(Y, g256.multiply(prod_li, y0));
            }
            return Y;
        }

        vector<pair<byte, byte>> get_shard_points(int byte_id) {
            vector<pair<byte, byte>> shard_points;
            for(int shard_id = 1; shard_id <= n_shards; shard_id++) {
                shard_points.push_back({(byte) shard_id, shards[shard_id][byte_id]});
            }
            return shard_points;
        }

        byte reconstruct_from_shrad_points(vector<pair<byte, byte>> shard_points) {
    	
        	if(shard_points.size() < k) {
	    		throw 300;
    		}
        	return lagrange_evaluate(shard_points);
        
        }

        byte reconstruct_byte(int byte_id) {
            auto shard_points = get_shard_points(byte_id);
            return reconstruct_from_shrad_points(shard_points);
        }
};

int main() {
    
    string test_secret = "my secret message";
    int n_shards = 4;
    int min_req = 2;
    shamir_secret sss(test_secret, n_shards, min_req);

    ////////////////// Tests ///////////////////////////


    // Test1: Reconstruction (byte - by - byte)
    string recovered = "";
    for(int i = 0; i < test_secret.size(); i++) {
      recovered += sss.reconstruct_byte(i);
    }
    cout << "found: " << recovered << endl;
    assert(recovered == test_secret);

    // Test2: Reconstruction for 0th byte ("m") using random shard points
    
    vector<pair<byte, byte>> byte0_shards =  sss.get_shard_points(0);
	assert(byte0_shards.size() == n_shards);
	
	// Test 2.1: use 1st, 2nd shard points
	vector<pair<byte, byte>> test_byte0_shards = {byte0_shards[0], byte0_shards[1]};
	byte found_byte = sss.reconstruct_from_shrad_points(test_byte0_shards);
	assert(test_secret[0] == found_byte);
	cout << "0th byte :" << found_byte << endl;

	// Test 2.2: use 2nd, 4rh shard points
	test_byte0_shards = {byte0_shards[1], byte0_shards[3]};
	found_byte = sss.reconstruct_from_shrad_points(test_byte0_shards);
	assert(test_secret[0] == found_byte);
	cout << "0th byte :" << found_byte << endl;

	// Test 2.3: use 3rd, 4th shard points
	test_byte0_shards = {byte0_shards[2], byte0_shards[3]};
	found_byte = sss.reconstruct_from_shrad_points(test_byte0_shards);
	assert(test_secret[0] == found_byte);
	cout << "0th byte :" << found_byte << endl;
    
    // Test 2.4 Using 1st, 2nd, 4th shard points in different orders
	test_byte0_shards = {byte0_shards[0], byte0_shards[1], byte0_shards[3]};
	found_byte = sss.reconstruct_from_shrad_points(test_byte0_shards);
	assert(test_secret[0] == found_byte);
	cout << "0th byte :" << found_byte << endl;
    

	test_byte0_shards = {byte0_shards[1], byte0_shards[3], byte0_shards[2]};
	found_byte = sss.reconstruct_from_shrad_points(test_byte0_shards);
	assert(test_secret[0] == found_byte);
	cout << "0th byte :" << found_byte << endl;
    
	// Test 3:Trying 1 shard point
	test_byte0_shards = {byte0_shards[3]};
	try {
		found_byte = sss.reconstruct_from_shrad_points(test_byte0_shards);
		cout << "0th byte :" << found_byte << endl;
	}
	catch(...) {
		cout << "Provide min " << min_req << " shard_points";
	}
	

	return 0;
}
