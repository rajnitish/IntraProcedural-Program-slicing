#include <stdio.h>
int main()
{

  // Test Case 1 
    int n = 1;
    int i = 1;
    int sum = 0;
    int product = 1;

    while (i <= n)
    {
        sum = sum+i;
        product = product*i;
        i++;
    }
    printf("%d",sum);
    printf("%d",product);

   
   //Test Case 2
        /* 
   int a = 1;
   int b = 2;
   int c = 3;
   int d = b+1;
   int e = c+d;
   */


      return 0;
}
