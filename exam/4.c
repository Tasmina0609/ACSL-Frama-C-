/*@ requires taille>0;
    requires \valid(t+(0..taille-1));
    assigns \nothing; 

    ensures (\forall integer i; 0<=i<taille ==> t[i] > t[i+1]) ==> \result==0;
    ensures (\forall integer i; 0<=i<taille ==> t[i] < t[i+1]) ==> \result==0;
    
*/

int monotonic(int t[], int taille) {
      int inc=1,dec=1;
/*@ loop invariant 0<=i<=taille-1;
    loop invariant (\forall integer j; 0<=j<i-1 ==> t[j] > t[j+1]) ==> inc==0;
    loop invariant (\forall integer j; 0<=j<i-1 ==> t[j] < t[j+1]) ==> dec==0;
    loop variant taille-1-i;
*/
      for(int i=0;i<taille-1;i++) {
            if ( t[i] > t[i+1])  
                 inc=0;
            if ( t[i] < t[i+1]) 
                 dec=0;
      }
      return inc || dec;
}
