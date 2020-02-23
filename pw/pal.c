/*@ requires n>0;
    requires \valid(a+(0..n-1));

    behavior success:
    ensures \forall integer i; 0<=i<n ==> a[i]==a[n-i-1];
    ensures \result==1;

    behavior failure:
    ensures \exists integer i; 0<=i<n && a[i]!=a[n-i-1];
    ensures \result==0;
*/

int palindrome(int a[],int n) {
/*@ loop invariant 0<=i<=n;
    loop invariant \forall integer j; 0<=j<i ==> a[j]==a[n-j-1];
    loop variant n-i;
*/
      for(int i=0;i<n;i++) {
            if(a[i]!=a[n-i-1]) return 0;
      }
      return 1;
}     