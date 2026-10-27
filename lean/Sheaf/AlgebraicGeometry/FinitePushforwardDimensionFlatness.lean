module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Finite direct image and dimension-filtered base flatness

Source: Stacks Project, flat.tex, Tag 05UF, finite-direct-image paragraph;
coherent.tex, Tag 02KG; algebra.tex, Tag 00HT; spaces-flat.tex, Tag 0CWS
(blueprint: lem-sfb-finite-pushforward-dimension-flatness).

For a test T over S, W_T is W times_S T and Z_T is Z times_W W_T, the canonical
iterated model of Z times_S T. All modules below are the actual tensor pullbacks.
The base-change assertion uses the canonical adjunction-defined map, not an
unspecified isomorphism. Pointwise flatness uses restriction of scalars along
stalkMap, including the composite map on Z_T.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite direct image preserves finite-type quasi-coherence and, after every base
change, preserves and reflects stalkwise and dimension-filtered base flatness.
The final two clauses test the threshold on all etale scheme charts and on any
single surjective etale atlas, respectively. An empty fibre is a vacuous universal
quantifier and does not require surjectivity of h.

Source: Stacks Project, Tags 05UF, 02KG, 00HT and 0CWS
(blueprint: lem-sfb-finite-pushforward-dimension-flatness).

Proof (the seven DAG steps):
1. Finite h is affine by definition. Thus affine base change gives that E=h_*G is quasi-coherent
   and identifies its pullback along W_T\to W canonically with h_{T,*}G_T for every T\to S. To
   check finite type, work on V=\operatorname{Spec}A\subset W with h^{-1}V=\operatorname{Spec}B.
   The affine finite-type criterion makes M=\Gamma(h^{-1}V,G) a finite B-module. Choose A-module
   generators b_i of B and B-module generators m_j of M. Every element of M is an A-linear
   combination of the finitely many b_im_j. Since E(V)=M, the same affine criterion proves that
   E is of finite type.
   Uses: def-weil-finite-integral-morphism, lem-weil-pbc-affine-pushforward-base-change, lem-
   weil-pbc-quasi-coherent-finite-type-affine.
2. Fix T\to S and w\in W_T over t\in T. Finite base change makes h_T finite; tensor pullback
   preserves quasi-coherence and finite type, so the previous step applies on T. Put R=\mathcal
   O_{T,t}. Choose an affine neighbourhood V=\operatorname{Spec}A of w and write
   h_T^{-1}V=\operatorname{Spec}B, p\subset A for w, and M=\Gamma(h_T^{-1}V,G_T). Put
   C=(A\setminus p)^{-1}B and N=(A\setminus p)^{-1}M. The affine module-stalk presentation
   identifies (E_T)_w with A_p\otimes_A M=N, compatibly with the action of R\to A_p. For a point
   z above w, corresponding to q\subset B, it identifies (G_T)_z with M_q, compatibly with the
   same base action. Here the tensor-to-fraction identification sends (a/s)\otimes m to am/s and
   m/s to (1/s)\otimes m.
   Uses: lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-module-pullback-quasi-coherent,
   lem-weil-pbc-module-pullback-finite-type, lem-pc-intrinsic-flat-module-stalk-tensor-
   presentation, lem-weil-pbc-affine-open-stalk-localization, def-weil-pbc-module-localization.
3. The localized algebra C is finite over the local ring A_p: the fractions b_i/1 of the finite
   generators of B still generate, by clearing the common scalar denominator. Base change of a
   ring localization identifies C with B\otimes_A A_p. Every maximal ideal Q of C therefore
   contracts to pA_p. The localization-prime statement says that q=Q\cap B is prime, disjoint
   from the image of A\setminus p, and Q=qC. The preimage of Q in A is p, since Q\cap A_p=pA_p.
   Thus q is precisely a point z\in h_T^{-1}(w). This argument needs neither a surjective map
   h_T nor a nonempty fibre.
   Uses: lem-weil-pbc-localization-base-change, lem-weil-pbc-finite-algebra-local-radical, lem-
   weil-pbc-localization-quotient-by-prime.
4. For any q\subset B over p, all scalar denominators from A\setminus p avoid q. Localizing N
   further at the image of B\setminus q gives M_q: the maps are (m/s)/(b/1)\mapsto m/(sb) and
   m/b\mapsto(m/1)/(b/1). The equivalence relation on fractions verifies these formulas are
   inverse and R-linear. If Q is maximal in C and q=Q\cap B, every element of C\setminus Q is
   b/s with b\notin q; inverting these is the same as inverting b/1, since s/1 is already a
   unit. Consequently N_Q=M_q as R-modules as well.
   Uses: def-weil-pbc-module-localization.
5. If (E_T)_w=N is R-flat, localizing this C-module at the image of B\setminus q preserves
   R-flatness. Step 4 identifies the result with (G_T)_z=M_q for every point over w. Conversely,
   if all these stalks are R-flat, Step 3 assigns such a point to every maximal Q\subset C, and
   Step 4 identifies N_Q with its stalk. The maximal-localization flatness test gives that N is
   R-flat. This also proves the empty-fibre case: there are then no maximal ideals of C by Step
   3, so the same test applies with a vacuous hypothesis. Thus the claimed stalk equivalence
   holds for every w.
   Uses: lem-pc-affine-flat-module-localization-preserves-flatness, lem-sfb-base-flatness-
   maximal-localizations.
6. Finite h_T is integral. Its affine residue-field extensions \kappa(w)\to\kappa(z) are
   therefore algebraic. The transcendence-degree tower formula and its algebraicity criterion
   give \operatorname{trdeg}_{\kappa(t)}\kappa(z)=\operatorname{trdeg}_{\kappa(t)}\kappa(w).
   Suppose E_T satisfies the threshold condition and take z above w with degree at least n: the
   degree equality and Step 5 give flatness at z. Conversely, for w of degree at least n, every
   point above it has the same degree and is flat by the condition on G_T; Step 5 gives flatness
   at w, including when that fibre is empty. This proves the threshold equivalence for every
   n\geq0.
   Uses: pqf-lem-finite-integral-lft, lem-a1-integral-residue-extension-algebraic, lem-kun-
   transcendence-degree-tower.
7. Finally W_T\to T is locally of finite type by base change. So is Z_T\to T: on any affine base
   chart, choose a finite-type affine chart \operatorname{Spec}A of W_T; its inverse image has
   coordinate algebra B finite as an A-module. A finite set of module generators of B, together
   with a finite set of algebra generators of A over the base chart, generates B as a base
   algebra. The pullbacks of E and G are finite-type quasi-coherent modules by Step 2. Apply the
   dimension-flatness chart criterion separately to (W_T,E_T) and (Z_T,G_T): on each, the
   intrinsic pointwise condition is equivalent to testing all etale scheme charts and also to
   testing any one surjective etale scheme atlas. Substituting these two equivalences into Step
   6 gives exactly the last clause. The identity chart shows directly that no pointwise
   condition is lost for schemes.
   Uses: lem-weil-pbc-lft-base-change, def-weil-finite-type-morphism, lem-sfb-space-dimension-
   flatness-base-change-sheaf.
-/
theorem finitePushforward_dimension_flatness {S W Z : Scheme.{u}}
    (f : W ⟶ S) [LocallyOfFiniteType f] (h : Z ⟶ W) [IsFinite h]
    (G : Z.Modules) (hG : G.IsQuasiCoherentFiniteType) :
    ((pushforward h).obj G).IsQuasiCoherentFiniteType ∧
    ∀ (T : Scheme.{u}) (g : T ⟶ S),
      IsIso (moduleBaseChangeMap h (pullback.snd h (pullback.fst f g)) (pullback.fst f g)
        (pullback.fst h (pullback.fst f g))
        (pullback.condition (f := h) (g := pullback.fst f g)) G) ∧
      (∀ w : (Limits.pullback (C := Scheme.{u}) f g), @Module.Flat (T.presheaf.stalk
        ((pullback.snd f g) w))
        ((RingedSpace.moduleStalkFunctor (Limits.pullback (C := Scheme.{u}) f g).toRingedSpace
        w).obj ((tensorPullback
        (pullback.fst f g)).obj ((pushforward h).obj G))) _ _ (Module.compHom _ ((pullback.snd f
        g).stalkMap w).hom) ↔
        ∀ z : (Limits.pullback (C := Scheme.{u}) h (pullback.fst f g)), (pullback.snd h
        (pullback.fst f g)) z = w →
        @Module.Flat (T.presheaf.stalk (((pullback.snd h (pullback.fst f g)) ≫ (pullback.snd f g))
        z)) ((RingedSpace.moduleStalkFunctor (Limits.pullback (C := Scheme.{u}) h (pullback.fst f
        g)).toRingedSpace
        z).obj
        ((tensorPullback (pullback.fst h (pullback.fst f g))).obj G)) _ _ (Module.compHom _
        (((pullback.snd h (pullback.fst f g)) ≫ (pullback.snd f g)).stalkMap z).hom)) ∧
      (∀ n : ℕ,
        ((∀ z : (Limits.pullback (C := Scheme.{u}) h (pullback.fst f g)), (n : Cardinal.{u}) ≤
        @Algebra.trdeg
        (T.residueField (((pullback.snd h (pullback.fst f g)) ≫ (pullback.snd f g)) z))
        ((Limits.pullback
        h (pullback.fst f g)).residueField z) _ _ (((pullback.snd h (pullback.fst f g)) ≫
        (pullback.snd f g)).residueFieldMap z).hom.toAlgebra → @Module.Flat (T.presheaf.stalk
        (((pullback.snd h (pullback.fst f g)) ≫ (pullback.snd f g)) z))
        ((RingedSpace.moduleStalkFunctor (Limits.pullback (C := Scheme.{u}) h (pullback.fst f
        g)).toRingedSpace z).obj
        ((tensorPullback (pullback.fst h (pullback.fst f g))).obj G)) _ _ (Module.compHom _
        (((pullback.snd h (pullback.fst f g)) ≫ (pullback.snd f g)).stalkMap z).hom)) ↔ (∀ w :
        (Limits.pullback (C := Scheme.{u}) f g), (n : Cardinal.{u}) ≤ @Algebra.trdeg
        (T.residueField ((pullback.snd
        f g)
        w)) ((Limits.pullback (C := Scheme.{u}) f g).residueField w) _ _ ((pullback.snd f
        g).residueFieldMap
        w).hom.toAlgebra → @Module.Flat (T.presheaf.stalk ((pullback.snd f g) w))
        ((RingedSpace.moduleStalkFunctor (Limits.pullback (C := Scheme.{u}) f g).toRingedSpace
        w).obj ((tensorPullback
        (pullback.fst f g)).obj ((pushforward h).obj G))) _ _ (Module.compHom _ ((pullback.snd f
        g).stalkMap w).hom))) ∧
        ((∀ (U : Scheme.{u}) (a : U ⟶ (Limits.pullback (C := Scheme.{u}) h (pullback.fst f g))),
        Etale a → (∀ x : U,
        (n :
        Cardinal.{u}) ≤ @Algebra.trdeg (T.residueField ((a ≫ ((pullback.snd h (pullback.fst f g))
        ≫ (pullback.snd f g))) x)) (U.residueField x) _ _ ((a ≫ ((pullback.snd h (pullback.fst f
        g)) ≫ (pullback.snd f g))).residueFieldMap x).hom.toAlgebra → @Module.Flat
        (T.presheaf.stalk ((a ≫ ((pullback.snd h (pullback.fst f g)) ≫ (pullback.snd f g))) x))
        ((RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj ((tensorPullback a).obj
        ((tensorPullback (pullback.fst h (pullback.fst f g))).obj G))) _ _ (Module.compHom _ ((a ≫
        ((pullback.snd h (pullback.fst f g)) ≫ (pullback.snd f g))).stalkMap x).hom))) ↔
          (∀ (V : Scheme.{u}) (b : V ⟶ (Limits.pullback (C := Scheme.{u}) f g)), Etale b → (∀ y :
        V, (n :
        Cardinal.{u}) ≤
        @Algebra.trdeg (T.residueField ((b ≫ (pullback.snd f g)) y)) (V.residueField y) _ _ ((b ≫
        (pullback.snd f g)).residueFieldMap y).hom.toAlgebra → @Module.Flat (T.presheaf.stalk ((b
        ≫ (pullback.snd f g)) y)) ((RingedSpace.moduleStalkFunctor V.toRingedSpace y).obj
        ((tensorPullback b).obj ((tensorPullback (pullback.fst f g)).obj ((pushforward h).obj
        G)))) _ _ (Module.compHom _ ((b ≫ (pullback.snd f g)).stalkMap y).hom)))) ∧
        (∀ (U V : Scheme.{u}) (a : U ⟶ (Limits.pullback (C := Scheme.{u}) h (pullback.fst f g)))
        (b : V ⟶
        (Limits.pullback (C := Scheme.{u}) f g)),
          Etale a → Surjective a → Etale b → Surjective b →
          ((∀ x : U, (n : Cardinal.{u}) ≤ @Algebra.trdeg (T.residueField ((a ≫ ((pullback.snd h
        (pullback.fst f g)) ≫ (pullback.snd f g))) x)) (U.residueField x) _ _ ((a ≫ ((pullback.snd
        h (pullback.fst f g)) ≫ (pullback.snd f g))).residueFieldMap x).hom.toAlgebra →
        @Module.Flat (T.presheaf.stalk ((a ≫ ((pullback.snd h (pullback.fst f g)) ≫ (pullback.snd
        f g))) x)) ((RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj ((tensorPullback a).obj
        ((tensorPullback (pullback.fst h (pullback.fst f g))).obj G))) _ _ (Module.compHom _ ((a ≫
        ((pullback.snd h (pullback.fst f g)) ≫ (pullback.snd f g))).stalkMap x).hom)) ↔ (∀ y : V,
        (n : Cardinal.{u}) ≤ @Algebra.trdeg (T.residueField ((b ≫ (pullback.snd f g)) y))
        (V.residueField y) _ _ ((b ≫ (pullback.snd f g)).residueFieldMap y).hom.toAlgebra →
        @Module.Flat (T.presheaf.stalk ((b ≫ (pullback.snd f g)) y))
        ((RingedSpace.moduleStalkFunctor V.toRingedSpace y).obj ((tensorPullback b).obj
        ((tensorPullback (pullback.fst f g)).obj ((pushforward h).obj G)))) _ _ (Module.compHom _
        ((b ≫ (pullback.snd f g)).stalkMap y).hom))))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
