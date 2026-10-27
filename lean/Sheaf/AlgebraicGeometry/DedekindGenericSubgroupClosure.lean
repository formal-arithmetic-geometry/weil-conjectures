module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Closure of a generic subgroup over a Dedekind domain

Source: BLR, Néron Models, §10.1, Proposition 4, proof, p.291; compare §7.1,
Corollary 6, p.175; Stacks Project, Tags 01R6, 01R8 and 0AUW.
(blueprint: lem-sfb-dedekind-lft-generic-subgroup-closure).

Group schemes are group objects in the category of schemes over the base.
The generic fibre and its group structure are transported by `Over.pullback`.
For an affine open `U` of `M`, the inverse image of `U` under
`j.left ≫ pullback.fst M.X.hom _` is canonically `U_E ×_{M_E} J`.
The kernel of the section map of a closed immersion is its defining ideal on `U`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The schematic closure of a closed finite-type generic subgroup is a separated,
commutative, flat, locally finite-type subgroup, with its specified generic fibre and
universal factorization from arbitrary flat schemes.

Source: BLR, Néron Models, §10.1, Proposition 4, proof, p.291, and §7.1, Corollary 6,
p.175; Stacks Project, Tags 01R6, 01R8 and 0AUW.
(blueprint: lem-sfb-dedekind-lft-generic-subgroup-closure).

Proof plan:
1. The map `a : J → M` is quasi-compact: over an affine `U` its inverse image is
   closed in the affine `U_E`. Take its scheme-theoretic image (node
   lemma-nagata-scheme-image-ideal-qc). Section injectivity for the image gives
   exactly the displayed kernel ideal, compatible with restriction and gluing.
2. On an affine chart put `T = D \ {0}`. The ideal is the contraction of the ideal
   of `J ∩ U_E` in `T⁻¹B`; extending it back recovers that ideal. Thus the generic
   fibre equals `J`. The quotient embeds in an `E`-algebra and is D-torsion-free.
3. Apply lem-sfb-dedekind-torsionfree-module-flat to these affine quotients, then
   lem-weil-pbc-flat-local-ring-maps to their local rings, giving flatness.
4. For flat `X`, use lem-weil-pbc-flat-morphism-affine-criterion and
   lem-trf-flat-module-torsionfree-domain on affine opens. A pulled-back element of
   the closure ideal vanishes after localization, hence is killed by a nonzero
   scalar and is zero. Descend the ring map to the quotient. Local factorizations
   agree and glue uniquely because a closed immersion is a monomorphism.
5. The base, `C`, and `C ×_S C` are flat, using
   lem-weil-pbc-flat-morphism-base-change and lem-pc-flat-compose. Apply step 4 to
   the ambient identity, inverse and multiplication, whose generic fibres land
   in the subgroup `J`, obtaining operations on `C` compatible with its inclusion.
6. Cancel that inclusion in the group diagrams of `M` to get associativity,
   units, inverses and commutativity (def-sc-group-scheme).
7. Over every affine open of the base, quotienting the finitely generated affine
   coordinate algebras gives local finite type on `C`. Its diagonal is the
   pullback of the closed diagonal of `M`, so it is separated. -/
theorem exists_dedekind_generic_subgroup_closure
    (D : Type u) [CommRing D] [IsDedekindDomain D] (_hDdim : ringKrullDim D = 1)
    (E : Type u) [Field E] [Algebra D E] [IsFractionRing D E]
    (M : Grp (Over (Spec (CommRingCat.of D)))) [IsCommMonObj M.X]
    [IsSeparated M.X.hom] [LocallyOfFiniteType M.X.hom]
    (J : Grp (Over (Spec (CommRingCat.of E))))
    (j : J.X ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).obj M.X)
    [IsMonHom j] [IsClosedImmersion j.left]
    [LocallyOfFiniteType J.X.hom] [QuasiCompact J.X.hom] :
    ∃ (C : Grp (Over (Spec (CommRingCat.of D)))) (i : C.X ⟶ M.X),
      IsMonHom i ∧ IsClosedImmersion i.left ∧ IsCommMonObj C.X ∧
      IsSeparated C.X.hom ∧ Flat C.X.hom ∧ LocallyOfFiniteType C.X.hom ∧
      (∀ U : M.X.left.affineOpens,
        RingHom.ker (i.left.app U).hom =
          RingHom.ker ((j.left ≫ pullback.fst M.X.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D E)))).app U).hom) ∧
      (∃ e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).obj C.X ≅ J.X,
        e.hom ≫ j = (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).map i) ∧
      (∀ (X : Over (Spec (CommRingCat.of D))) (_hX : Flat X.hom) (f : X ⟶ M.X),
        (∃ g : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).obj X ⟶ J.X,
          g ≫ j = (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).map f) →
        ∃! g : X ⟶ C.X, g ≫ i = f) := by
  sorry

end AlgebraicGeometry
