/*@ requires taille>0;
    requires \valid(t+(0..taille-1));
    assigns \nothing; 

    behavior success:
      assumes \forall integer i; 0<=i<taille-1 ==> t[i]<=t[i+1];
      ensures \result==1;

    behavior failure:
      assumes \exists integer i; 0<=i<taille-1 && t[i]>t[i+1];
      ensures \result==0;
*/

int increasing(int t[], int taille){
/*@   loop invariant 0<=i<=taille-1;
      loop invariant \forall integer j; 0<=j<i ==> t[j]<=t[j+1];
      loop variant taille-i;  
*/
      for(int i=0;i<taille-1;i++) {
            if( (t[i] > t[i+1]) )  return 0;
      }
      return 1; 
}
