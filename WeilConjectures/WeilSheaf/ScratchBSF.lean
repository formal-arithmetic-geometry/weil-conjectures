module
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericRep
open AlgebraicGeometry
variable {C : Scheme} [IsIntegral C]
set_option pp.explicit true in
#synth CommRing (SeparableClosure (Scheme.functionField C))
set_option pp.explicit true in
#synth Field (SeparableClosure (Scheme.functionField C))
