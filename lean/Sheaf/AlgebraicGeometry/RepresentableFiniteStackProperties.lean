module

public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.DMIsomSpaceUnramified
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-! # Representable finite morphisms to Deligne--Mumford stacks

Source: Stacks Project, algebraic.tex, Tags 045G and 05UM; spaces-morphisms.tex,
Tags 04NZ and 04NY; stacks-morphisms.tex, Lemma 06UA and discussion after 0CL5
(blueprint: lem-sfb-representable-finite-stack-properties).

The source is assumed to be a stack, and the target is Deligne--Mumford. The finite
hypothesis retains every scheme test and its projection. Properness and local
quasi-finiteness use the intrinsic stack definitions, also applicable to coarse morphisms.

The imported shared predicates supply field-valued points, atlas-detected closed sets,
finite type, quasi-compactness, universal closedness, and relative-diagonal tests.
Source for these predicates: Stacks, stacks-properties.tex, definition-points and
lemma-topology-points; stacks-morphisms.tex, definitions separated, quasi-compact,
locally-finite-type, proper (0CL5), and locally-quasi-finite (06PU).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A stack finite and representable over a DM stack is DM, and the map is proper
and locally quasi-finite. Local quasi-finiteness includes local finite type.
Source: Stacks, algebraic.tex, Tags 045G and 05UM; spaces-morphisms.tex, 04NZ and 04NY;
stacks-morphisms.tex, 06UA and discussion after 0CL5
(blueprint: lem-sfb-representable-finite-stack-properties).

Proof:
1. For y₁,y₂ over T, the DM target supplies the algebraic space
I = Isom_X(v y₁,v y₂) (`lem-sfb-dm-isom-space-unramified`). Put
P = Y ×_X T using v y₁; it is a finite scheme over T. The maps I → P are
(y₁,id) and (y₂,α⁻¹), where α is the universal isomorphism on I.
2. The algebraic-space fibre product E = I ×_(P ×_T P) P exists by
`lem-trf-space-fibre-products-etale-covers`. Its test points are precisely α admitting
a lift β : y₁ ≅ y₂ with v β = α. The lift is unique since P is represented by a
scheme, hence has no relative automorphisms. Thus E represents Isom_Y(y₁,y₂),
so the diagonal of Y is representable by algebraic spaces.
3. Pull back an etale surjective scheme atlas U → X. Its pullback V → U is
finite, hence V is a scheme. For every T → Y, T ×_Y V identifies with T ×_X U:
compose the specified isomorphisms; conversely insert the given object of Y(T).
Hence V → Y is etale and surjective on all tests. Together with step 2 and hY,
this makes Y Deligne--Mumford. No flatness or surjectivity of v is needed.
4. Every scheme projection v_T is finite. It is proper by
`lem-weil-pbc-finite-proper` and quasi-finite by `pqf-lem-finite-qf`;
finiteness also supplies local finite type, so it is locally quasi-finite in
`pqf-def-quasifinite`, including at every point of every nonreduced test.
5. Apply the representable compatibility of
`lem-sfb-representable-stack-property-tests`: the tests of step 4 imply properness
and local quasi-finiteness as stack morphisms, including the diagonal and point-space
conditions. The signature retains the intrinsic predicates, so this compatibility is a genuine
bridge in the proof, rather than a definitional replacement of its conclusions.
The empty source, identity maps and non-surjective finite maps are all allowed. -/
theorem representableFinite_stack_properties (S : Scheme.{u})
    (X : BasedCategory.{v₁, w₁} (Over S)) (Y : BasedCategory.{v₂, w₂} (Over S))
    (v : BasedFunctor Y X) (hX : IsDeligneMumfordModuliStack X)
    (hY : IsModuliStack Y) (hv : IsRepresentableFiniteModuliMap v) :
    IsDeligneMumfordModuliStack Y ∧
      IsProperModuliMap v ∧
      IsLocallyQuasiFiniteModuliMap v := by
  sorry

end CategoryTheory
