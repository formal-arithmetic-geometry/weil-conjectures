/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import Sheaf.FieldTheory.FieldTower
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.GenericFibreIsoSpreadBaseOpen
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finite equivariant quasi-splitting of a nodal family

Source: de Jong, Families of curves and alterations (1997), Lemmas 5.6--5.7,
pp. 614--615, and Theorem 5.9 proof, p. 617
(blueprint: lem-sfb-nodal-finite-quasi-splitting).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- An already semistable family becomes quasi-split after a finite, surjective,
generically etale equivariant base change. The kernel fixed field is precisely the image
of the original function field under the generic-stalk map of the finite cover.
The group actions may be nonfaithful and semilinear over the field.

Source: de Jong (1997), Lemmas 5.6--5.7, pp. 614--615
(blueprint: lem-sfb-nodal-finite-quasi-splitting).

Proof (the node's ten steps):
1. For a finitely presented nodal family $g:C\to V$, write $D_g$ and $B_g$ for its singular
   subscheme and its two-branch cover. The branch-cover lemma identifies $(B_g)_v$ with the
   inverse image of the singular points in $C_v^\nu$, and $B_g\to D_g$ has two geometric points
   over each geometric node. The finite etale field-algebra decomposition identifies its finite
   branch fibre with a product of its finite separable residue fields. Thus $C_v$ is quasi-split
   exactly when $(B_g)_v$ is a disjoint union of rational points. Indeed rationality of both
   branches is part of the definition; conversely a rational branch above $x$ forces
   $\kappa(v)\to\kappa(x)$ to be an isomorphism since its composite with $\kappa(x)\to\kappa(b)$
   is an isomorphism. This criterion includes the empty branch scheme.
   Uses: lem-sfb-nodal-branch-double-cover, lem-weil-pbc-etale-algebra-over-field-product.
2. First prove the base-change clause, independently of the alteration. For $V'\to V$ and
   $v'\mapsto v$, put $F=\kappa(v)$ and $L=\kappa(v')$. The branch-cover identifications give
   $(B_{g_{V'}})_{v'}=(B_g)_v\times_F L$. If $C_v$ is quasi-split, this is a disjoint union of
   copies of $\operatorname{Spec}L$, because $F\otimes_F L=L$. Step 1 now makes the singular
   points and both normalization branches $L$-rational. This argument is local at each fibre and
   does not assume that $V'$ is Noetherian or that normalization of the total space commutes
   with base change.
   Uses: lem-sfb-nodal-branch-double-cover.
3. The base $S$ is Noetherian: a field is a Noetherian ring and finite type over a Noetherian
   scheme is Noetherian. It has finite topological dimension by the finite-type dimension lemma.
   The same holds for every intermediate normal integral projective finite-type $k$-base. Regard
   $f$ as a semistable multipointed curve with empty marking. Its base changes remain flat
   finitely presented nodal families by the semistable base-change lemma; projectivity is
   preserved by base change, and a projective morphism is proper. Consequently the branch scheme
   is finite over each intermediate base. We will prove the assertion more generally for such
   families by induction on the dimension of the closure of their non-quasi-split locus, without
   using smoothness of their generic fibres.
   Uses: lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, lem-trf-
   semistable-marked-base-change, lem-pc-projective-base-change, lem-pc-projective-proper, lem-
   sfb-nodal-branch-double-cover.
4. We need the spreading claim of Lemma 5.7. Let $T$ be any integral reduced closed subscheme of
   an intermediate base $V$, with generic point $\xi$, and suppose $C_\xi$ is quasi-split.
   Restrict to a nonempty affine open $T_0\subset T$. The finite scheme $B_g\times_V T_0$ is
   affine, and is finitely presented over $T_0$ by finite-over-locally-Noetherian finite
   presentation. By Step 1 its generic fibre is isomorphic to the generic fibre of
   $\coprod_{j=1}^n T_0$, including $n=0$. Apply generic-fibre isomorphism spreading to these
   two affine finitely presented $T_0$-schemes. It gives a nonempty open $U\subset T_0$ on which
   the branch scheme is $\coprod_{j=1}^n U$. Step 1 proves that every fibre over $U$ is quasi-
   split.
   Uses: lem-sfb-nodal-branch-double-cover, pqf-lem-finite-fp-locnoeth, lem-sbc-generic-fibre-
   iso-spread-base-open.
5. Let $A\subset V$ be the set of points with non-quasi-split fibre, and let $Z=\overline A$
   with its reduced closed structure. If $Z=\varnothing$, use the identity cover and the
   identity group surjection. Otherwise $Z$ has finitely many irreducible components; write
   $s_1,\ldots,s_r$ for their generic points. None has quasi-split fibre. To see this, if $s_i$
   did, Step 4 would give an open neighbourhood of $s_i$ inside its component on which all
   fibres are quasi-split. Delete the other finitely many components and shrink inside that
   open. The result is a nonempty relatively open subset of $Z$ disjoint from $A$, contradicting
   $\overline A=Z$.
   Uses: lem-weil-pbc-noetherian-finitely-many-components.
6. Apply equivariant finite residue domination on $V$, with its current finite group $G$, at the
   points $s_i$, to the finite etale residue schemes $E_i=(B_g)_{s_i}$. Obtain $a:W\to V$ and
   $\sigma:J\twoheadrightarrow G$. The base $W$ is normal integral projective of finite type
   over $k$; $a$ is finite surjective generically etale and $k(W)^{\ker\sigma}=k(V)$. Every
   fibre over every point of $a^{-1}(s_i)$ is quasi-split by the prescribed splitting, the
   branch-cover base-change identification and Step 1. Give $C\times_V W$ the action
   $j(c,w)=(\sigma(j)c,jw)$. Its projection and its map to $C$ are equivariant because the two
   coordinates have the same image in $V$.
   Uses: lem-sfb-equivariant-finite-residue-domination, lem-sfb-nodal-branch-double-cover.
7. Write $A_W$ for the bad locus on $W$ and $Z_W=\overline{A_W}$. Step 2 implies $A_W\subset
   a^{-1}(A)$ and hence $Z_W\subset a^{-1}(Z)$. No point $w$ of $Z_W$ lies over any $s_i$.
   Otherwise take a generic point $z$ of a component of $Z_W$ containing $w$. Its image
   generalizes $s_i$ and belongs to $Z$, so $a(z)=s_i$. Finiteness implies integrality;
   incomparability for integral maps then gives $z=w$ (use an affine neighbourhood of $s_i$,
   whose inverse image contains both points). Step 6 makes the fibre at $w$ quasi-split.
   Applying the argument of Step 5 to the family on $W$ says that a maximal point of $Z_W$
   cannot have quasi-split fibre, a contradiction.
   Uses: lem-weil-pbc-noetherian-finitely-many-components, pqf-lem-finite-integral-lft, pqf-lem-
   incomparability.
8. Put $d=\dim Z$. Every specialization chain of points of $Z_W$ maps to a strict chain in $Z$:
   equality between contractions of two comparable points would contradict incomparability. By
   Step 7 the first image point is not a maximal point of $Z$, so the image chain can be
   extended at its generic end by the generic point of a component of $Z$. Therefore its length
   is at most $d-1$. This proves $\dim Z_W<d$; in particular $Z_W$ is empty if $d=0$. This chain
   argument also handles reducible $Z$ and requires no flatness of the finite cover.
   Uses: pqf-lem-finite-integral-lft, pqf-lem-incomparability, lem-weil-pbc-noetherian-finitely-
   many-components.
9. Induct strongly on the nonnegative integer $d$ of Step 8, with empty bad closure as the
   initial case of Step 5. For the inductive step apply the induction hypothesis to the family
   on $W$, whose bad closure has smaller dimension. It gives a further normal projective finite
   cover $c:S'\to W$ with group $L\twoheadrightarrow J$, all fibres quasi-split, and
   $k(S')^{\ker(L\to J)}=k(W)$. Compose the two surjections and the two finite covers. Finite
   morphisms compose, surjectivity composes as surjectivity of point maps, and etale composition
   proves that the composite is generically etale: intersect its two etale loci on $W$ and
   remove the image of their closed complement in $V$ under the finite map. That image is
   closed: on every affine target open use closedness of the spectrum map of its finite integral
   affine inverse image. It misses the generic point: the generic fibre of the finite dominant
   map $W\to V$ is the spectrum of a finite-dimensional domain over $k(V)$, hence a field and
   thus just the generic point of $W$. Thus all geometric and equivariance requirements persist
   through the induction.
   Uses: lem-trf-finite-radicial-basechange, lem-weil-pbc-etale-composition-cancellation, lem-
   weil-pbc-integral-spec-closed-map, lem-weil-pbc-finite-dimensional-domain-is-field.
10. For completeness check the fixed field through this composition. Write $K=k(V)$, $M=k(W)$
   and $F=k(S')$. If $P=\ker(L\to J)$ and $R=\ker(L\to G)$, then $P\triangleleft R$,
   $R/P=\ker(J\to G)$ (surjectivity of $L\to J$), and $F^P=M$. An element of $F$ fixed by $R$ is
   exactly an element of $M$ fixed by $\ker(J\to G)$. Hence $F^R=M^{\ker(J\to G)}=K$. This is
   just the definition of a fixed subfield. Start the induction with $V=S$, $G=H$ and $C=Q$. The
   resulting composite supplies $b:S'\to S$, its group surjection and the asserted kernel fixed
   field. Its pulled-back family is exactly $Q\times_S S'$ by associativity of fibre products.
   Its fibres are quasi-split by the induction, and the final arbitrary-base-change assertion
   was proved in Step 2.
-/
theorem exists_finite_equivariant_quasiSplitNodalFibres
    (k : Type u) [Field k] (S Q : Scheme.{u})
    (pS : S ⟶ Spec (.of k)) [IsIntegral S] [IsHProjective pS]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : Q ⟶ S) [IsHProjective f] [Flat f] [LocallyOfFinitePresentation f]
    (hnodal : HasNodalGeometricFibres f)
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ S),
      IsReduced (pullback f g) ∧ (pullback f g).IsPureDimension 1)
    [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    [GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S))]
    (H : Type v) [Group H] [Finite H]
    (σk : H →* (k ≃+* k)) (σQ : H →* Aut Q) (σS : H →* Aut S)
    (hS : ∀ h : H, (σS h).hom ≫ pS =
      pS ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (hQ : ∀ h : H, (σQ h).hom ≫ f ≫ pS =
      f ≫ pS ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (heq : ∀ h : H, (σQ h).hom ≫ f = f ≫ (σS h).hom) :
    ∃ (J : Type (max u v)) (_ : Group J) (_ : Finite J) (ρ : J →* H),
      Function.Surjective ρ ∧
      ∃ (S' : Scheme.{u}) (_ : IsIntegral S') (b : S' ⟶ S)
        (τS : J →* Aut S') (τQ : J →* Aut (pullback f b)),
        IsHProjective (b ≫ pS) ∧
        (∀ s : S', IsDomain (S'.presheaf.stalk s) ∧
          IsIntegrallyClosed (S'.presheaf.stalk s)) ∧
        IsFinite b ∧ Surjective b ∧
        (∃ U : S.Opens, Dense (U : Set S) ∧ Etale (b ∣_ U)) ∧
        (∀ j : J, (τS j).hom ≫ b = b ≫ (σS (ρ j)).hom) ∧
        (∀ j : J, (τQ j).hom ≫ pullback.fst f b =
          pullback.fst f b ≫ (σQ (ρ j)).hom) ∧
        (∀ j : J, (τQ j).hom ≫ pullback.snd f b =
          pullback.snd f b ≫ (τS j).hom) ∧
        (∃ hb : b (genericPoint S') = genericPoint S,
          ∀ z : S'.functionField,
            (∃ a : S.functionField,
              (S.presheaf.stalkSpecializes (specializes_of_eq hb) ≫
                b.stalkMap (genericPoint S')).hom a = z) ↔
              ∀ j : ρ.ker, (Scheme.functionFieldAut (τS j.val)).hom z = z) ∧
        HasQuasiSplitNodalFibres (pullback.snd f b) := by
  sorry

/-- Quasi-splitting of a nodal family is preserved by an arbitrary base change.
There is no normality, projectivity, generic-fibre or Noetherian hypothesis on either base.

Source: de Jong (1997), definition preceding Lemma 5.7, pp. 614--615, and the
base-change preservation used in the proof of Theorem 5.9, p. 617
(blueprint: lem-sfb-nodal-finite-quasi-splitting).

Proof: this is Step 2 of the node, using the branch criterion from Step 1. The relative
branch double cover of lem-sfb-nodal-branch-double-cover commutes with base change and
identifies its fibre with the inverse image of the singular points in the normalized fibre.
Over a residue field F, quasi-splitting says that the finite branch fibre is a disjoint
union of copies of Spec F, including the empty union. After a residue-field extension
F → L it becomes a disjoint union of copies of Spec L, since F tensor_F L = L.
Thus both branches are L-rational. The intermediate residue field of the singular point
also equals L, as its map into either rational branch factors an isomorphism of fields.
This proves exactly the singular-point and branch rationality conditions at every new
base point, including smooth fibres. Normalization of the total space is not used. -/
theorem HasQuasiSplitNodalFibres.baseChange
    {Q S : Scheme.{u}} (f : Q ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hnodal : HasNodalGeometricFibres f)
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ S),
      IsReduced (pullback f g) ∧ (pullback f g).IsPureDimension 1)
    (hquasi : HasQuasiSplitNodalFibres f) (S' : Scheme.{u}) (b : S' ⟶ S) :
    HasQuasiSplitNodalFibres (pullback.snd f b) := by
  sorry

end AlgebraicGeometry
