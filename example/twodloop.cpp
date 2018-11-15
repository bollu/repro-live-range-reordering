#define N  100
void foo(int A[N][N]) {
    int t[1];
    for(int j = 2; j <= 3; j++) {
        for(int i = 1; i <= 2; i++) {
S1:         t[0] = i * j;
S3:          A[i][j] = t[0];
        }
    }
}
