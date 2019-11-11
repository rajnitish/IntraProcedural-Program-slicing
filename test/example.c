#include <stdio.h>
int main()
{

    // Test Case 1
    /* int n = 1;
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
        
   int a = 1;
   int b = 2;
   int c = 3;
   int d = b+1;
   int e = c+d;
  

    // Test case 3
    int a = 1;
    int b = 2;
    int c = 3;
    int d = 3;
    int e = 5;

    if (a > 2)
        d = b + 1;
    else
        e = c + d;
*/
    // Test Case 4

    int a = 6;
    int b = 2;
    int c = 3;
    int d = 3;
    int e = 5;

    while (a != e)
    {
        if (a > 2)
        {
            d = b + 1;
    
        }
        else
        {
            e = b + d;
    
        }
        
    }


    printf("%d",d );
    printf("%d",e);

    return 0;
}
