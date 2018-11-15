#define N 200
void foo(int A[N][N], int t[2*N], int C[N][N], int B[N][N], int n) {
 for ( int i = 0; i < n; ++ i)
            for ( int j = 0; j < n; ++ j) {
    S1 : t [i + j] = A[i ][ j ];
    S2 : C [i ][ j ] = t [i + j ];
            }
        for ( int i = 0; i < n; ++ i)
            for ( int j = 0; j < n; ++ j) {
    S3 : t [i + j] = B[i ][ j ];
    S4 : C [j ][ i ] += t[i + j ];
            }
}
/*
void foo(int A[N][N]) {
    int t[1];
    for(int j = 2; j <= 3; j++) {
        for(int i = 1; i <= 2; i++) {
S1:         t[0] = i * j;
S3:          A[i][j] = t[0];
        }
    }
}
*/
