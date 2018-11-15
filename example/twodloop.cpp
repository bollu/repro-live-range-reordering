
#define N  2
void foo(int A[N][N] ) {
    for(int i = 0; i < N; i++) {
        for(int j = 1; j < N; j++) {
            int t = A[i][j - 1];
            if (t < 0) { t = 0; }
            A[i][j] = t;
        }
    }
}
