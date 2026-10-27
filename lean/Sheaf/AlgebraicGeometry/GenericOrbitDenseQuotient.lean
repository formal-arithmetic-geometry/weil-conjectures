/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.FieldTheory.FieldTower
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Topology.Sober
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.RingHom.PurelyInseparable
import Sheaf.AlgebraicGeometry.AdmissibleFiniteTypeFieldQuotient
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.FieldTheory.PowerInBaseAfterLocalization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Dense open universal homeomorphisms from generic geometric orbits

Source: ILO, Travaux de Gabber, X 2.3 Step 2, printed p. 151; IX 1.4, pp. 132--133;
Stacks Project, Tags 02NW, 01S4, and 04DF
(blueprint: lem-sfb-generic-orbit-dense-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every subgroup has a finite reduced admissible geometric categorical quotient. For the
full group its generic fibres are finite purely inseparable fields, and its map to the base
is a finite universal homeomorphism over a dense open containing every component generic.
The finite disjoint integral open cover presents the base's integral components. The binder
`t` in the geometric-generic hypothesis is identified with the canonical algebraic-closure
point, so the action maps are specified on the actual geometric fibre by both projections.

Source: ILO, Travaux de Gabber, X 2.3 Step 2, printed p. 151; IX 1.4, pp. 132--133;
Stacks Tags 02NW, 01S4, and 04DF (blueprint: lem-sfb-generic-orbit-dense-quotient).

Proof plan:
1. First $Y$ is separated over $e$. Indeed its locally closed immersion $j:Y\hookrightarrow
   P=\mathbf P^n_e$ is a monomorphism. Thus $\Delta_{Y/e}$ is the pullback of $\Delta_{P/e}$ along
   $j\times j:Y\times_eY\to P\times_eP$: the pullback is $Y\times_PY=Y$. Projective space is
   separated and closed immersions remain closed after base change. This checks the separatedness
   hypothesis of the quotient theorem without imposing any separatedness condition on $B$.
   Uses: lem-weil-pbc-projective-space-proj-separated, lem-weil-pbc-closed-immersion-base-change,
   def-weil-proper-morphism.
2. For every $H\leq G$, apply the finite-type field quotient theorem to $Y/e$ and the restricted
   action. Its final clause supplies admissibility for every such action because $Y$ is
   quasi-projective. It gives a finite surjective $q_H:Y\to Q_H$, the orbit geometric fibres,
   topological quotient, invariant structure sheaf, categorical property for all scheme targets,
   and reducedness of $Q_H$. Invariance of $h$ gives a unique factor $d_H:Q_H\to B$ with
   $d_Hq_H=h$. These properties are exactly the admissible quotient definition. The identity
   $h=d_Hq_H$ and surjectivity of $h$ imply surjectivity of $d_H$.
   Uses: lem-sfb-admissible-finite-type-field-quotient, def-per-admissible-finite-scheme-quotient.
3. A field is Noetherian, and finite type over a Noetherian scheme is Noetherian; hence $B$ and
   $Y$ are Noetherian, in particular quasi-compact and locally Noetherian, so both are
   quasi-separated. Since $Y\to\operatorname{Spec}e$ factors as $Y\to B\to\operatorname{Spec}e$
   and is of finite type, $h$ is locally of finite type. As $Y$ is quasi-compact and
   quasi-separated and $B$ is quasi-separated, $h$ is quasi-compact and quasi-separated. Let
   $\eta$ be the generic point of a component $B_i$ and $\bar\eta$ the geometric point over it.
   The projection $Y_{\bar\eta}\to Y_\eta$ is surjective, being the base change of the surjection
   $\operatorname{Spec}\overline{\kappa(\eta)}\to\operatorname{Spec}\kappa(\eta)$, and $Y_\eta$ is
   homeomorphic to $h^{-1}(\eta)$. The underlying points of $Y_{\bar\eta}$ form one orbit of the
   finite group $G$, so they are finitely many; hence $h^{-1}(\eta)$ is finite. The
   generic-finiteness lemma now gives a dense open $V\subseteq B$ containing every generic point
   with $h^{-1}V\to V$ finite. By the last relative clause of the quotient theorem,
   $Q_G\times_BV\to V$ is also finite. For each of the finitely many components $B_i$, choose a
   nonempty affine $U_i=\operatorname{Spec}A_i\subseteq V\cap B_i$; then $A_i$ is a Noetherian
   domain. These opens are disjoint and contain all generic points.
   Uses: lem-weil-pbc-finite-type-over-noetherian,
   lem-weil-pbc-locally-noetherian-quasi-separated, lemma-nagata-finite-type-to-separated-target,
   lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-surjective-base-change,
   def-pc-scheme-fibre, def-weil-geometric-fibre,
   lem-weil-pbc-generic-finite-morphism-open-neighborhood,
   lem-sfb-admissible-finite-type-field-quotient.
4. Fix $U_i=\operatorname{Spec}A$, put $K=\operatorname{Frac}A$, and write
   $Q_G\times_BU_i=\operatorname{Spec}C$. Finiteness and base change give the generic fibre
   $\operatorname{Spec}D$, where $D=C\otimes_AK=(A\setminus\{0\})^{-1}C$ is finite-dimensional
   over $K$. The ring $C$ is reduced by Step 2, so $D$ is reduced: if $(c/a)^n=0$, some nonzero
   $b\in A$ kills $c^n$; then $(bc)^n=0$, whence $bc=0$ and $c/a=0$. Choose an algebraic closure
   $\Omega/K$. The base change $Y_{\bar\eta}\to(Q_G)_{\bar\eta}$ is surjective. All points of its
   source lie in one $G$-orbit, and invariance makes their images equal; therefore its target is a
   singleton. Also $(Q_G)_{\bar\eta}\to(Q_G)_\eta$ is surjective, being the base change of the
   surjection $\operatorname{Spec}\Omega\to\operatorname{Spec}K$. Thus $\operatorname{Spec}D$ is a
   nonempty singleton, in particular irreducible. The irreducible-spectrum criterion makes the
   nilradical of $D$ prime. Reducedness makes it zero, so $D$ is a domain. A finite-dimensional
   domain over a field is a field; denote it by $L$.
   Uses: lem-weil-pbc-finite-morphism-permanence, def-weil-finite-integral-morphism,
   lem-weil-pbc-surjective-base-change, lem-zl-spectrum-irreducible-nilradical-prime,
   lem-weil-pbc-finite-dimensional-domain-is-field.
5. We show $L/K$ is purely inseparable. The finite algebra $D\otimes_K\Omega$ has singleton
   spectrum by Step 4. Its residue field is a finite-dimensional extension of $\Omega$: the
   quotient by its prime is a finite-dimensional domain, hence already a field. Such an extension
   of an algebraically closed field is trivial. Consequently there is exactly one $\Omega$-point
   of this singleton scheme, equivalently exactly one $K$-algebra map $t:L\to\Omega$. Existence
   can also be read directly from the integral geometric-point existence lemma applied to the zero
   prime of $L$, since the finite map $K\to L$ is integral. Apply the unique-geometric-point
   pure-residue lemma to $K\to L$, this $t$, and $K\to\Omega$. Every competing extension with the
   same kernel equals $t$, as just proved; both kernels are zero. The residue fields are therefore
   $K$ and $L$, and its conclusion is precisely that $L/K$ is purely inseparable. This proves the
   asserted generic-fibre clause for every $B_i$.
   Uses: lem-weil-pbc-finite-dimensional-domain-is-field,
   lem-weil-pbc-alg-closed-finite-extension-trivial, lem-weil-pbc-finite-algebra-is-integral,
   lem-dl-a1-integral-geometric-point-existence, lem-dl-a1-unique-geometric-point-pure-residue.
6. To apply the power-localization lemma we must check that $C$ itself is a domain, not merely its
   generic algebra. Write $h^{-1}U_i=\operatorname{Spec}S$, finite over $A$. This is an invariant
   open, so its quotient is $\operatorname{Spec}(S^G)$ and $C=S^G\subseteq S$. The ring $S$ is
   reduced. Each minimal prime of $S$ is the generic point of a component of this open of $Y$ and
   hence maps to the generic point of $\operatorname{Spec}A$. Thus every nonzero $a\in A$ lies in
   no minimal prime of $S$. By the reduced-zerodivisor criterion multiplication by $a$ on $S$ is
   injective. It is then injective on $C\subseteq S$ as well. The fraction criterion for
   localization gives an injection $C\hookrightarrow C\otimes_AK=L$. Surjectivity of $h$ ensures
   $S\ne0$, so the same argument makes $A\hookrightarrow C$ injective. Hence $C$ is a domain, and
   $\operatorname{Frac}C=L$: the localization $C\otimes_AK$ is already a field, every fraction
   $c/a$ belongs to $\operatorname{Frac}C$, and every inverse of a nonzero element of $C$ belongs
   to this field. No commutation of invariants with nonflat base change was used.
   Uses: lem-sfb-admissible-finite-type-field-quotient,
   lem-weil-pbc-reduced-zerodivisors-union-minimal-primes, def-pc-reduced-scheme.
7. Now $A$ is a Noetherian domain, $C$ is a finite $A$-algebra which is a domain, and their
   fraction fields are $K\subseteq L$ with $L/K$ finite purely inseparable. Apply the
   power-in-base localization lemma to obtain $s_i\in A\setminus\{0\}$. In characteristic zero it
   identifies $C[1/s_i]$ with $A[1/s_i]$. In characteristic $p>0$, each $c\in C[1/s_i]$ has
   $c^{p^n}$ in the base ring for some $n$. If two homomorphisms from $C[1/s_i]$ to any field
   agree on $A[1/s_i]$, their values on $c$ have equal $p^n$-th powers, hence are equal: in a
   field $(u-v)^{p^n}=0$ implies $u=v$. Thus maps from the spectrum of any field into the source
   over the base are unique. The field-valued-point criterion for radicial morphisms therefore
   makes $\operatorname{Spec}C[1/s_i]\to\operatorname{Spec}A[1/s_i]$ universally injective; in
   characteristic zero it is already an isomorphism.
   Uses: lem-weil-pbc-power-in-base-after-localization, def-weil-radicial-morphism.
8. Set $U=\coprod_iD(s_i)\subseteq B$. Each $s_i$ is nonzero in the component domain, so $D(s_i)$
   is nonempty and contains its generic point; their union is dense and contains every generic
   point of $B$. Restriction preserves finiteness of both $h$ and $d_G$, by finite base change.
   Surjectivity of $d_G$ from Step 2 persists under restriction by the surjective-base-change
   lemma, applied to the open immersion $U\hookrightarrow B$. A finite morphism is integral by the
   finite-algebra integrality theorem on each affine chart. Step 7 makes $d_G$ universally
   injective on these disjoint target components, hence globally (after any base change, points
   with the same image lie over the same component). The integral-radicial-surjective criterion
   now says that $Q_G\times_BU\to U$ is a universal homeomorphism. All quotient properties were
   supplied before shrinking and hold for every subgroup, while the generic field calculation of
   Steps 4--5 applies to every integral component.
   Uses: lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-finite-algebra-is-integral,
   lem-pc-integral-radicial-surjective-universal-homeomorphism,
   lem-weil-pbc-surjective-base-change.
-/
theorem exists_generic_orbit_dense_quotient
    (e : Type u) [Field e] (B Y : Scheme.{u})
    (b : B ⟶ Spec (.of e)) (p : Y ⟶ Spec (.of e))
    [LocallyOfFiniteType b] [QuasiCompact b]
    [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced Y]
    (n : ℕ) (Bᵢ : Fin (n + 1) → B.Opens)
    (hcover : iSup Bᵢ = ⊤)
    (hdisjoint : ∀ i j : Fin (n + 1), i ≠ j → Disjoint (Bᵢ i) (Bᵢ j))
    (hintegral : ∀ i : Fin (n + 1), IsIntegral (Bᵢ i).toScheme)
    (hp : IsQuasiProjective p)
    (G : Type v) [Group G] [Finite G] (a : G →* Aut Y)
    (ha : ∀ g : G, (a g).hom ≫ p = p)
    (h : Y ⟶ B) (hh : h ≫ b = p) (hprojective : IsProjectiveBundle h)
    [Surjective h] (hinvariant : ∀ g : G, (a g).hom ≫ h = h)
    (hgeneric : ∀ (C : Set Y), C ∈ irreducibleComponents Y →
      ∀ ξ : Y, IsGenericPoint ξ C →
        (∃ D : Set B, D ∈ irreducibleComponents B ∧ IsGenericPoint (h ξ) D) ∧
          (h.residueFieldMap ξ).hom.Finite)
    (horbit : ∀ (D : Set B), D ∈ irreducibleComponents B →
      ∀ (η : B), IsGenericPoint η D →
      ∀ (t : Spec (.of (AlgebraicClosure (B.residueField η))) ⟶ B),
        t = Spec.map (CommRingCat.ofHom
          (algebraMap (B.residueField η) (AlgebraicClosure (B.residueField η)))) ≫
            B.fromSpecResidueField η →
        Nonempty ↥(pullback h t) ∧
        ∀ x y : ↥(pullback h t), ∃ (g : G) (l : pullback h t ⟶ pullback h t),
          l ≫ pullback.fst h t = pullback.fst h t ≫ (a g).hom ∧
          l ≫ pullback.snd h t = pullback.snd h t ∧ l x = y) :
    ∃ (Q : Subgroup G → Scheme.{u}) (q : ∀ H : Subgroup G, Y ⟶ Q H)
      (d : ∀ H : Subgroup G, Q H ⟶ B),
      (∀ H : Subgroup G,
        IsAdmissibleFiniteSchemeQuotient (a.comp H.subtype) (q H) ∧
        Surjective (q H) ∧ q H ≫ d H = h ∧ IsReduced (Q H) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Q H),
          Nonempty ↥(pullback (q H) t) ∧
          ∀ x y : ↥(pullback (q H) t),
            ∃ (g : H) (l : pullback (q H) t ⟶ pullback (q H) t),
              l ≫ pullback.fst (q H) t = pullback.fst (q H) t ≫ (a g).hom ∧
              l ≫ pullback.snd (q H) t = pullback.snd (q H) t ∧ l x = y) ∧
        ∀ (Z : Scheme.{u}) (f : Y ⟶ Z),
          (∀ g : H, (a g).hom ≫ f = f) → ∃! r : Q H ⟶ Z, q H ≫ r = f) ∧
      (∃ U : B.Opens, Dense (U : Set B) ∧
        (∀ (D : Set B), D ∈ irreducibleComponents B →
          ∀ η : B, IsGenericPoint η D → η ∈ U) ∧
        IsFinite (h ∣_ U) ∧ IsFinite (pullback.snd (d ⊤) U.ι) ∧
        (topologically IsHomeomorph).universally (pullback.snd (d ⊤) U.ι)) ∧
      ∀ (D : Set B), D ∈ irreducibleComponents B →
        ∀ η : B, IsGenericPoint η D →
        ∃ (L : Type u) (_ : Field L) (ι : B.residueField η →+* L),
          ι.Finite ∧ ι.IsPurelyInseparable ∧
          ∃ j : (d ⊤).fiber η ≅ Spec (.of L),
            j.hom ≫ Spec.map (CommRingCat.ofHom ι) = (d ⊤).fiberToSpecResidueField η := by
  sorry

end AlgebraicGeometry
