/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module
public import Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisFreeComplex
import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroAdjunction
/-! # Restriction data for the cartesian open-subscheme square

Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}

/-- The base change of the inclusion of an open subscheme.
Source: Stacks Project, Tag 04J0; the cartesian open-subscheme square.
(blueprint: lem-pc-open-restriction-data) -/
noncomputable def H.openBaseChangeInclusion (f : X ⟶ Spec (.of R)) (W : X.Opens) :
    baseChangedScheme (S := S) (W.ι ≫ f) ⟶ baseChangedScheme (S := S) f :=
  Limits.pullback.lift (baseChangeFst (S := S) (W.ι ≫ f) ≫ W.ι)
    (baseChangeSnd (S := S) (W.ι ≫ f)) (by
      dsimp [baseChangeFst, baseChangeSnd]
      rw [Category.assoc]
      exact Limits.pullback.condition)

/-- Degree-zero data for restriction, including the cartesian coefficient square.
Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
(blueprint: lem-pc-open-restriction-data)

Proof: Restriction along j = W.ι sends the free sheaf represented by W to the
free sheaf represented by the top open of W. This gives e by the Yoneda,
free/forgetful, and sheafification adjunctions. The underlying abelian sheaf of
j^*M is the restriction of the underlying abelian sheaf of M, because j is an
open immersion and its map of structure sheaves is an isomorphism. The
isomorphism d has as hom the abelian adjoint of the module pullback unit.
Its naturality for multiplication by a section gives the R-scalar square.
The base-changed inclusion k is an open immersion. The cartesian identity
k followed by p equals p_W followed by j gives c, the comparison between
the two composite inverse-image functors, by uniqueness of left adjoints to
the same composite direct-image functor. Composition of module pullbacks in
this square, followed by forgetting to abelian sheaves, gives d'. Naturality
for multiplication by sections from Spec S gives its S-scalar square. The
pullback units compose under these pullback comparisons. Taking abelian
adjoints proves the displayed coefficient square; this uses the unit and
counit identities, so the chosen c and d' are coherent. All data here are
sheaf morphisms in degree zero. No Ext equivalence or bijectivity is asserted.
For an empty open these are isomorphisms of zero sheaves; for the top open
they are the usual restriction identities. No flatness is used.
-/
theorem H.openRestrictionData (f : X ⟶ Spec (.of R)) (M : X.Modules) (W : X.Opens) :
    let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
    let G := invImage (baseChangeFst (S := S) f)
    let N := (SheafOfModules.toSheaf (baseChangedScheme (S := S) f).ringCatSheaf).obj
      (baseChangedModule (S := S) f M)
    let φ := coeff (baseChangeFst (S := S) f) (baseChangeUnit (S := S) f M)
    let ρ := (scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let τ := (scalarRep (baseChangedModule (S := S) f M)).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    let MW := (pullback W.ι).obj M
    let FW := (SheafOfModules.toSheaf W.toScheme.ringCatSheaf).obj MW
    let GW := invImage (baseChangeFst (S := S) (W.ι ≫ f))
    let NW := (SheafOfModules.toSheaf
      (baseChangedScheme (S := S) (W.ι ≫ f)).ringCatSheaf).obj
      (baseChangedModule (S := S) (W.ι ≫ f) MW)
    let φW := coeff (baseChangeFst (S := S) (W.ι ≫ f))
      (baseChangeUnit (S := S) (W.ι ≫ f) MW)
    let ρW := (scalarRep MW).comp
      (((Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ f).appTop).hom)
    let τW := (scalarRep (baseChangedModule (S := S) (W.ι ≫ f) MW)).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) (W.ι ≫ f)).appTop).hom)
    let J := invImage W.ι
    let J' := invImage (H.openBaseChangeInclusion (S := S) f W)
    ∃ (e : J.obj (H.openFreeSheaf W) ≅ H.openFreeSheaf (⊤ : W.toScheme.Opens))
      (d : J.obj F ≅ FW) (c : G ⋙ J' ≅ J ⋙ GW) (d' : J'.obj N ≅ NW),
      (∀ a, J.map (ρ a) ≫ d.hom = d.hom ≫ ρW a) ∧
      (∀ a, J'.map (τ a) ≫ d'.hom = d'.hom ≫ τW a) ∧
      J'.map φ ≫ d'.hom = (c.app F).hom ≫ GW.map d.hom ≫ φW := by sorry

end AlgebraicGeometry.Scheme.Modules
