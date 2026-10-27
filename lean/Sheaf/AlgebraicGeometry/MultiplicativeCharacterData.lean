module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.GroupTheory.Finiteness

/-! # Character antiduality: categories and canonical coordinate conditions

Source: Milne, Algebraic Groups (2017), Sections 12(a), 12(g), pp.230, 239--240
(blueprint: def-sfb-multiplicative-character-data).

The character group is specified by its actual group-scheme homomorphisms and
pointwise multiplication. Semilinear maps are characterized by both pullback
projections; hence the conditions below specify the canonical maps uniquely.
The invariant algebra is an intersection of equalizers of the displayed semilinear maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.MultiplicativeType

/-- The category in Milne Theorem 12.23, including non-smooth groups.
Source: Milne, pp.236, 240 (blueprint: def-sfb-multiplicative-character-data). -/
abbrev FiniteTypeGroups (k : Type u) [Field k] :=
  ObjectProperty.FullSubcategory (fun G : Grp (Over (Spec (.of k))) ↦
    IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom ∧
      IsMultiplicativeType G)

/-- Finitely generated discrete abelian Galois modules. Open stabilizers express
continuity for the discrete topology, with the Krull topology on the Galois group.
Source: Milne, Section 12(g), p.239 (blueprint: def-sfb-multiplicative-character-data). -/
abbrev CharacterModules (k ks : Type u) [Field k] [Field ks] [Algebra k ks] :=
  ObjectProperty.FullSubcategory
    (fun M : Action AddCommGrpCat.{u} (ks ≃ₐ[k] ks) ↦
      AddGroup.FG M.V ∧ ∀ m : M.V, IsOpen {σ : ks ≃ₐ[k] ks | (M.ρ σ).hom m = m})

/-- The canonical projection from a scalar extension to the original group scheme.
Source: Milne, Section 12(g) (blueprint: def-sfb-multiplicative-character-data). -/
abbrev scalarProjection {k F : Type u} [Field k] [Field F] [Algebra k F]
    (G : Grp (Over (Spec (.of k)))) :
    ((baseChange (K := F)).obj G).X.left ⟶ G.X.left :=
  pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k F)))

/-- Characters after scalar extension. The target is the scalar extension of the
recorded G_m, canonically G_m over F, with its pulled-back group law.
Source: Milne, p.239 (blueprint: def-sfb-multiplicative-character-data). -/
abbrev GeometricCharacters {k : Type u} (F : Type u) [Field k] [Field F] [Algebra k F]
    (G : Grp (Over (Spec (.of k)))) :=
  (baseChange (K := F)).obj G ⟶
    (baseChange (K := F)).obj (Grp.mk (StandardGroupSchemes.multiplicative k))

/-- The conjugation action on homomorphisms, characterized using the unique
semilinear endomorphisms of the two scalar extensions. The coordinate action is
σ(a e_m) = σ(a) e_(σ m); the orientation in the square accounts for contravariant Spec.
Source: Milne, pp.239--240 (blueprint: def-sfb-multiplicative-character-data). -/
def IsConjugate {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G T : Grp (Over (Spec (.of k)))}
    (σ : F ≃ₐ[k] F)
    (χ ψ : (baseChange (K := F)).obj G ⟶ (baseChange (K := F)).obj T) : Prop :=
  ∀ (a : ((baseChange (K := F)).obj G).X.left ⟶
      ((baseChange (K := F)).obj G).X.left)
    (b : ((baseChange (K := F)).obj T).X.left ⟶
      ((baseChange (K := F)).obj T).X.left),
    a ≫ scalarProjection G = scalarProjection G →
    a ≫ ((baseChange (K := F)).obj G).X.hom =
      ((baseChange (K := F)).obj G).X.hom ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) →
    b ≫ scalarProjection T = scalarProjection T →
    b ≫ ((baseChange (K := F)).obj T).X.hom =
      ((baseChange (K := F)).obj T).X.hom ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) →
    a ≫ χ.hom.hom.left = ψ.hom.hom.left ≫ b

/-- Extension of a character along compatible embeddings of closures. Each comparison
map is uniquely determined by its projections to the original scheme and the old closure.
Source: Milne, Theorem 12.23 and Corollary 12.25, p.240
(blueprint: def-sfb-multiplicative-character-data). -/
def IsCharacterExtension {k K ks Ks : Type u} [Field k] [Field K] [Field ks] [Field Ks]
    [Algebra k K] [Algebra k ks] [Algebra k Ks] [Algebra K Ks] [Algebra ks Ks]
    [IsScalarTower k K Ks] [IsScalarTower k ks Ks]
    {G T : Grp (Over (Spec (.of k)))}
    (χ : (baseChange (K := ks)).obj G ⟶ (baseChange (K := ks)).obj T)
    (ψ : (baseChange (K := Ks)).obj ((baseChange (K := K)).obj G) ⟶
      (baseChange (K := Ks)).obj ((baseChange (K := K)).obj T)) : Prop :=
  ∀ (a : ((baseChange (K := Ks)).obj ((baseChange (K := K)).obj G)).X.left ⟶
      ((baseChange (K := ks)).obj G).X.left)
    (b : ((baseChange (K := Ks)).obj ((baseChange (K := K)).obj T)).X.left ⟶
      ((baseChange (K := ks)).obj T).X.left),
    a ≫ scalarProjection G =
      scalarProjection ((baseChange (K := K)).obj G) ≫ scalarProjection G →
    a ≫ ((baseChange (K := ks)).obj G).X.hom =
      ((baseChange (K := Ks)).obj ((baseChange (K := K)).obj G)).X.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ks Ks)) →
    b ≫ scalarProjection T =
      scalarProjection ((baseChange (K := K)).obj T) ≫ scalarProjection T →
    b ≫ ((baseChange (K := ks)).obj T).X.hom =
      ((baseChange (K := Ks)).obj ((baseChange (K := K)).obj T)).X.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ks Ks)) →
    a ≫ χ.hom.hom.left = ψ.hom.hom.left ≫ b

/-- The semilinear coefficient-and-label action on L[M], as a k-algebra map.
Source: Milne, p.240 (blueprint: def-sfb-multiplicative-character-data). -/
def semilinearGroupAlgebra {k L : Type u} [Field k] [Field L] [Algebra k L]
    (M : AddCommGrpCat.{u}) (ρ : (L ≃ₐ[k] L) →* End M) (σ : L ≃ₐ[k] L) :
    AddMonoidAlgebra L M →ₐ[k] AddMonoidAlgebra L M :=
  (AddMonoidAlgebra.mapDomainAlgHom k L (ρ σ).hom).comp
    (AddMonoidAlgebra.mapAlgHom M σ.toAlgHom)

/-- The actual invariant coordinate algebra L[M]^Gal(L/k).
Source: Milne, p.240 (blueprint: def-sfb-multiplicative-character-data). -/
def invariantGroupAlgebra {k L : Type u} [Field k] [Field L] [Algebra k L]
    (M : AddCommGrpCat.{u}) (ρ : (L ≃ₐ[k] L) →* End M) :
    Subalgebra k (AddMonoidAlgebra L M) :=
  ⨅ σ : L ≃ₐ[k] L, AlgHom.equalizer (semilinearGroupAlgebra M ρ σ) (AlgHom.id k _)

/-- Spectrum of a specified Hopf structure on the invariant algebra.
Source: Milne, p.240 (blueprint: def-sfb-multiplicative-character-data). -/
def invariantHopfGroup {k L : Type u} [Field k] [Field L] [Algebra k L]
    (M : AddCommGrpCat.{u}) (ρ : (L ≃ₐ[k] L) →* End M)
    (h : HopfAlgebra k (invariantGroupAlgebra M ρ)) : Grp (Over (Spec (.of k))) :=
  letI := h
  (hopfSpec (.of k)).obj (op (CommHopfAlgCat.of k (invariantGroupAlgebra M ρ)))

/-- A descended Hopf model on the specified invariant algebra. Its group structure
is fixed by requiring the scalar-extension isomorphism to induce the inclusion
L[M]^Gal(L/k) → L[M] on coordinates. This determines every descended Hopf operation.
Source: Milne, Theorem 12.23, p.240
(blueprint: def-sfb-multiplicative-character-data). -/
structure InvariantHopfModel {k L : Type u} [Field k] [Field L] [Algebra k L]
    (M : AddCommGrpCat.{u}) (ρ : (L ≃ₐ[k] L) →* End M) where
  /-- The descended Hopf structure, determined by scalar extension. -/
  hopf : HopfAlgebra k (invariantGroupAlgebra M ρ)
  /-- Scalar extension to L is the indexed group algebra with its standard Hopf law. -/
  split : (baseChange (K := L)).obj
    (invariantHopfGroup M ρ hopf) ≅
      diagonalizableGroup L M
  /-- The splitting map is induced by the invariant-algebra inclusion. -/
  split_projection : split.inv.hom.hom.left ≫ scalarProjection
    (invariantHopfGroup M ρ hopf) =
      Spec.map (CommRingCat.ofHom (invariantGroupAlgebra M ρ).val.toRingHom)


/-- The Laurent coordinate t pulled back by a character. The target can itself be a
scalar extension of the original multiplicative group.
Source: Milne, Sections 12(a)--(b), pp.230--232
(blueprint: def-sfb-multiplicative-character-data). -/
def characterElement {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G : Grp (Over (Spec (.of F)))}
    (χ : G ⟶ (baseChange (K := F)).obj
      (Grp.mk (StandardGroupSchemes.multiplicative k))) : Γ(G.X.left, ⊤) :=
  χ.hom.hom.left.appTop
    ((scalarProjection (Grp.mk (StandardGroupSchemes.multiplicative k))).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1)))

end AlgebraicGeometry.MultiplicativeType
