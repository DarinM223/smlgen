infix &

datatype (*a*) ((*b*)'a(*c*), (*d*)'b(*e*)) (*f*)stmt(*g*) =
  (*h*)Assign(*i*) of (*j*)'a(*k*) * (*l*)((*m*)'a(*n*), (*o*)'b(*p*)) (*q*)expr(*r*)
| (*s*)If(*t*) of (*u*)((*v*)'a(*w*), (*x*)'b(*y*)) (*z*)expr (*1*) * (*2*)((*3*)'b(*4*), (*5*)'a(*6*)) (*7*)stmt (*8*)list (*9*) * (*10*)((*11*)'a(*12*), (*13*)'b(*14*)) (*15*)stmt(*16*) list(*17*)
and (*18*)((*19*)'b(*20*), (*21*)'a(*22*)) (*23*)expr(*24*) = (*25*)
  (*26*)Stmt (*27*) of (*28*)((*29*)'a(*30*), (*31*)'a(*32*)) (*33*)stmt(*34*)
| (*35*)Int (*36*) of (*37*)'b (*38*)
| (*39*)Bop (*40*)of (*41*)((*42*)'b(*43*), (*44*)'a(*45*)) (*46*)expr(*47*) * (*48*)((*49*)'a(*50*), (*51*)'b(*52*)) (*53*)expr(*54*)

datatype (*55*)((*56*)'a(*57*),(*58*)'b(*59*))(*60*)stmt(*61*) = (*62*)Stmt(*63*) of (*64*){ (*65*)a: (*66*)int(*67*) * (*68*)'b(*69*), (*70*)b: (*71*)'a(*72*) } (*73*)* (*74*)'b(*75*)