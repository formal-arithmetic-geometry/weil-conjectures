module
import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageHomComp

open CategoryTheory AlgebraicGeometry
universe u

example {X : Scheme.{u}} {T S : Over X} (f : T ⟶ S) :
    (Over.mk f.left).left = T.left := rfl
