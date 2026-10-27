/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Sheaf.FieldTheory.FieldTower
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.GDelta.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import WeilConjectures.AlgebraicGeometry.DimensionBaseChange
import Sheaf.AlgebraicGeometry.NowhereDenseDimZero
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.NormalizationInseparableBaseChange
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.ProperBirationalNormalCurveIso
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import Sheaf.AlgebraicGeometry.GeonormalDimOneSmooth
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Sheaf.AlgebraicGeometry.NormalizationGeonormalInsep
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import WeilConjectures.Blowup.Extension
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

/-! # Equivariant flat preparation of a marked generic curve

Source: de Jong, Families of curves and alterations (1997), Sections 2.7--2.10,
printed pp. 603--605; ILO, Expose X, Theorem 3.4, proof Step 2, p. 160
(blueprint: lem-sfb-equivariant-flat-curve-preparation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Flat preparation retaining the given finite semilinear group action.
The generic fibre is taken over the generic stalk, so its base field is literally
`S.functionField`. Its normalization is specified over both the original curve and this field.
The tensor-product isomorphism is characterized on pure tensors by the induced generic maps.
The marking is the schematic closure specified by the kernel of restriction to the reduced
inverse image of `E` on that generic fibre. Empty markings are included.

Source: de Jong, Sections 2.7--2.10; ILO X, Theorem 3.4, proof Step 2
(blueprint: lem-sfb-equivariant-flat-curve-preparation).

Proof (the reviewed DAG's thirteen steps):
1. Put $X=C_\eta$, a proper geometrically integral curve over $K$. Apply [lem-weil-pbc-
   normalization-geonormal-insep] to choose a finite purely inseparable $K_1/K$ such that the
   normalization $N_1$ of $X_{K_1}$ is geometrically normal. The base change $X_{K_1}$ is integral
   by the geometric-integrality hypothesis. Its normalization is finite birational, integral and
   one-dimensional by [lem-sc-normalization-exists] and [lem-pc-dim-base-change]. Thus [lem-weil-
   pbc-geonormal-dim-one-smooth] makes $N_1$ smooth. It is geometrically integral: on an affine
   chart with coordinate domain $B$, its integral closure embeds in $\operatorname{Frac}(B)$;
   after any field extension that embedding remains injective and the latter tensor product is a
   localization of a geometrically integral affine chart of $X$. These domains have the same
   generic point, so their union is integral. The generic fibre description of $g$ also identifies
   $k(X)=F$.
2. Give the inverse image of $E$ in $N_1$ its reduced induced structure and call it $D_1$ [lem-
   weil-pbc-reduced-induced-closed-subscheme]. It omits the generic point: that point maps to the
   generic point of the integral scheme $C$, which is outside the nowhere dense $E$. The
   dimension-zero and finiteness lemmas [lem-pc-nowhere-dense-dim-zero] and [lem-pc-zero-
   dimensional-closed-subscheme-finite] make $D_1$ finite over $K_1$. It has finitely many
   irreducible components, since its finite-dimensional algebra is Noetherian and [lem-weil-pbc-
   noetherian-finitely-many-minimal-primes] applies. Choose a finite purely inseparable $K_2/K_1$
   making $(D_1\times_{K_1}K_2)_{\rm red}$ geometrically reduced by [lem-pur-finite-inseparable-
   geometric-reduction]. If $D_1$ is empty take $K_2=K_1$.
3. Extend each automorphism of $K$ uniquely to its perfect closure: in characteristic $p>0$ the
   image of $u$ with $u^{p^r}=v\in K$ is the unique $p^r$-root of the image of $v$. Put $K_0$
   equal to the compositum of all $h(K_2)$ for $h\in H$. There are finitely many generators, all
   purely inseparable over $K$, so $K_0/K$ is finite purely inseparable and $H$-stable; the unique
   extensions satisfy the group law. In characteristic zero all these fields are $K$. Let $N$ be
   the normalization of $X_{K_0}$. By [lem-trf-normalization-inseparable-base-change],
   $N=N_1\times_{K_1}K_0$, and the reduced inverse image $D$ of $E$ in $N$ is
   $(D_1\times_{K_1}K_0)_{\rm red}$. The preceding geometrically reduced finite scheme remains
   reduced after $K_0/K_2$, so $D$ is finite geometrically reduced. The same comparison preserves
   the smooth geometrically integral curve $N$.
4. Write $D=\operatorname{Spec}A$. The finite-dimensional reduced algebra $A$ is Noetherian, and
   each of its nonzerodivisors is a unit, since injective multiplication on a finite-dimensional
   vector space is surjective. Thus $Q(A)=A$. By [lem-weil-pbc-noetherian-finitely-many-minimal-
   primes] and [lem-weil-pbc-reduced-noetherian-total-ring-fractions], $A$ is a finite product of
   finite extension fields $L_j/K_0$. Each $L_j$ is geometrically reduced, being a direct factor
   after any scalar extension. If an element of $L_j$ had inseparable minimal polynomial, its
   algebra after extending to an algebraic closure would have a nonzero nilpotent. The injection
   of that algebra into $L_j$ remains injective after scalar extension (vector spaces are flat), a
   contradiction. Hence every $L_j/K_0$ is separable. The finite-etale algebra criterion [lem-sc-
   finite-etale-algebra-criterion] makes $D/K_0$ finite etale. The zero algebra gives the allowed
   empty product. Also $F_0=F\otimes_K K_0$ is a domain by geometric integrality of $X$, and
   finite-dimensional over $F$; [lem-weil-pbc-finite-dimensional-domain-is-field] makes it a
   field. It is the function field of $N$.
5. Normalize $Y$ in $K_0$ and $C$ in $F_0$ using [def-fin-normalization-extension], obtaining
   $S_0$ and $C_0$. They are finite over $Y$ and $C$ by [lem-fin-normalization-extension-finite].
   The integral-closure normality lemma makes them normal integral with these function fields.
   They carry genuine $H$-actions: an automorphism sends a monic equation over an affine chart to
   a monic equation over its translated chart, hence preserves the corresponding integral
   closures; restriction and composition are the field restriction and composition. The actions
   therefore glue. For $\operatorname{Spec}A\subset Y$ and $\operatorname{Spec}B\subset
   g^{-1}(\operatorname{Spec}A)$, each element of the integral closure of $A$ in $K_0$ is integral
   over $B$ in $F_0$. These inclusions define $C_0\to S_0$. The localization lemma [lem-weil-pbc-
   integral-closure-commutes-localization] makes the definitions compatible on overlaps and
   identifies its generic fibre with $N$. The equation over $Y$ is built into these ring
   inclusions.
6. The finite map $S_0\to Y$ and projectivity of $Y/k$ (H-projective and quasi-compact, since $Y$
   is of finite type over $k$, as in [def-pc-projective-morphism]) imply that $S_0/k$ is
   H-projective by [lem-fin-finite-over-projective], applied with affine base
   $\operatorname{Spec}k$. Graph argument: let $V$ be a $k$-scheme with a closed immersion
   $V\hookrightarrow\mathbf P^N_k$ over $k$ and let $V\to B$ be a $k$-morphism to a separated
   $k$-scheme $B$. The graph $V\to V\times_kB$ is the pullback of the diagonal of $B$, which is a
   closed immersion by separatedness [def-weil-proper-morphism], so it is a closed immersion [lem-
   weil-pbc-closed-immersion-base-change]. Base change of $V\hookrightarrow\mathbf P^N_k$ along
   $B\to\operatorname{Spec}k$ gives a closed immersion $V\times_kB\hookrightarrow\mathbf
   P^N_k\times_kB$, and the latter is $B\times_{\operatorname{Spec}\mathbf Z}\mathbf P^N_{\mathbf
   Z}=\mathbf P^N_B$ by associativity of fibre products [def-nagata-projective-space-base-change].
   The composite [lem-weil-pbc-closed-immersion-comp] is a closed immersion
   $V\hookrightarrow\mathbf P^N_B$ over $B$, so $V\to B$ is H-projective. Applied to $V=S_0$ and
   the separated (proper) $k$-scheme $B=Y$, it makes $S_0\to Y$ H-projective. The finite map
   $C_0\to C$ makes $C_0$ proper over $k$, since $C\to Y$ and $Y/k$ are proper. Consequently
   $C_0\to S_0$ is proper by [lem-weil-pbc-proper-to-separated]. Every finite-type scheme over $k$
   occurring here is Noetherian and excellent: fields are excellent, finite-type affine algebras
   are excellent, and excellence passes from an affine cover to all affine opens by the three
   cited excellence statements. These observations check the base hypotheses for flattening below.
7. Apply [lem-sfb-semilinear-equivariant-chow-modification] to $C_0/k$. Write $q:T\to C_0$ for the
   resulting integral equivariant projective birational model. Since $T/k$ is H-projective and
   $S_0/k$ is separated (it is H-projective, hence proper by [lem-pc-projective-proper]), the
   graph argument of Step 6 with $V=T$, $B=S_0$ makes $T\to S_0$ H-projective; it uses [lem-weil-
   pbc-closed-immersion-base-change], [def-nagata-projective-space-base-change] and [lem-weil-pbc-
   closed-immersion-comp]. The generic fibre $T_{\eta_0}$ is an integral curve with function field
   $F_0$: localization of the affine domains of the integral $T$ gives the generic fibre and
   preserves its function field. The dimension formula [lem-sc-closed-irreducible-dimension-trdeg]
   gives dimension one from this function field. Its proper birational morphism to the smooth
   normal curve $N$ is an isomorphism by [lem-trf-proper-birational-normal-curve-iso]. Thus $D$ is
   a finite etale closed subscheme of $T_{\eta_0}$. Let $L\subset T$ be its schematic closure; it
   is $H$-stable because its ideal is the kernel of restriction to the invariant generic
   subscheme. No equality with the whole inverse image of $E$ is asserted: vertical components are
   omitted.
8. Apply [lem-trf-flatification-horizontal-curve-pair] to $T\to S_0$ and $L$. Its hypotheses hold:
   $S_0$ is excellent integral Noetherian, $T\to S_0$ is H-projective with smooth irreducible one-
   dimensional generic fibre $N$, and $L$ is the closure of the finite etale $D$. It supplies a
   blowup $V=\operatorname{Bl}_{I}S_0\to S_0$ in a finite-type ideal $I$ equal to $\mathcal O$ on
   a dense open, and flat finitely presented strict transforms $T_V,L_V$. Their geometric fibres
   are pure of dimensions one and zero respectively, and $L_V\to V$ is finite. This application
   does not supply a group action on $V$.
9. Put $J=\prod_{h\in H}h(I)$ on $S_0$ and let $U$ be the intersection of the translates of a
   dense open on which $I=\mathcal O$; $U$ is an invariant dense open and $J|_U=\mathcal O$.
   Iterating [lemma-nagata-product-ideal-common-blowup], $B=\operatorname{Bl}_{J}S_0$ dominates
   every translated blowup, in particular $V$, and is $U$-admissible. The invariant $J$ gives an
   $H$-action on the Rees algebra $\bigoplus_nJ^n$, hence on $B$ by [prop-nagata-relative-proj-
   functoriality]. Over an affine $\operatorname{Spec}R\subset S_0$ the charts of $B$ are the
   degree-zero localizations $R[J/a]\subset\operatorname{Frac}R$, $0\neq a\in J(R)$ (part (1)), so
   $B$ is integral with function field $K_0$. The graded surjection
   $\operatorname{Sym}J\to\bigoplus_nJ^n$ gives a closed immersion $B\hookrightarrow\mathbf
   P_{S_0}(J)$ (part (3)), so $B\to S_0$ is projective in the bundle sense [def-trf-projective-
   bundle-morphism]. Projective $k$-schemes carry ample sheaves [lem-pc-very-ample-ample]; so
   $B\to S_0$ is H-projective [lem-trf-projective-bundle-to-h-projective] and $B/k$ is
   H-projective [lem-trf-h-projective-composition]. Let $\nu:S\to B$ be the normalization; it is
   finite and birational [lem-sc-normalization-exists], $S$ is normal integral [lem-weil-pbc-
   integral-closure-finite-extension-normal], and $\nu$ is bundle-projective [lem-trf-finite-
   projective-bundle], hence H-projective over the projective $B$, so $S/k$ is H-projective. The
   graph argument of Step 6 ($V=S$, separated $S_0$) makes $S\to S_0$ H-projective; it is
   birational. Normalization lifts the action by the monic-equation argument of Step 5. Thus
   $k(S)=K_0$ and $S\to V$ is defined, although it need not be equivariant.
10. Pull back $T_V$ and $L_V$ along $S\to V$, obtaining $P$ and $M$. Flatness is preserved by
   [lem-weil-pbc-flat-morphism-base-change]; projectivity by [lem-pc-projective-base-change], and
   finiteness by [lem-weil-pbc-finite-morphism-permanence]. Finite presentation is checked on
   affine charts: a presentation by finitely many generators and relations remains such after
   scalar extension, using [lem-weil-pbc-finite-presentation-base-change-composition](1).
   Geometric fibres are those of $T_V,L_V$ after extension of residue fields, hence retain their
   pure dimensions. Their generic fibres are $N,D$, since all modifications of $S_0$ were
   birational. In particular $M_\eta$ is finite etale. The closed immersion $M\hookrightarrow P$
   is the base change of $L_V\hookrightarrow T_V$.
11. Both $P$ and $M$ are schematically dense along their generic fibres. Indeed over any affine
   domain $A$ in $S$, flatness gives injectivity of $B\to B\otimes_A\operatorname{Frac}(A)$ on
   every affine chart $\operatorname{Spec}B$ of either scheme, by [lem-sc-flat-invertible-
   sections-torsion-free] applied to the structure sheaf. Consequently the kernels defining the
   closures of $N$ and $D$ are exactly the ideals already defining $P$ and $M$ inside
   $T\times_{S_0}S$. This identifies $P$ and $M$ intrinsically as those schematic closures,
   independently of the nonequivariant map $S\to V$. The actions on $T,S,N,D$ preserve these
   kernels, so give $H$-actions on $P,M$ and make every structural map equivariant. Each nonempty
   affine chart of $P$ embeds in the coordinate ring of its generic chart in the integral $N$, so
   is a domain. Every nonempty open meets that generic fibre by the same injectivity; its
   irreducibility thus proves $P$ integral. Its function field is $F_0$.
12. Set $f:P\to S$, let $b:S\to Y$ be the composite through $S_0$, and let $a:P\to C$ be the
   composite through $T,C_0$. All maps commute with the actions, and $ga=bf$ by their fibre-
   product construction. The projectivity of $S\to S_0$ and $S_0/k$, and [lem-trf-h-projective-
   composition], make $S/k$ H-projective. Since $f$ is H-projective, the same lemma makes $P/k$
   H-projective. The separated (proper) targets $Y/k$ and $C/k$ allow the graph argument of Step
   6, with [lem-weil-pbc-closed-immersion-base-change], [def-nagata-projective-space-base-change]
   and [lem-weil-pbc-closed-immersion-comp], to make $b$ and $a$ H-projective. Projectivity
   implies properness. Both are dominant, with function fields $K_0/K$ and $F_0/F$ finite.
   Properness makes their dense images closed and hence surjective. The dimension formula [lem-sc-
   closed-irreducible-dimension-trdeg] gives dimension zero for the integral finite-type generic
   fibres from these finite field extensions. A zero-dimensional integral scheme has just its
   generic point. Their generic fibres therefore have one point, so [lem-weil-pbc-generic-finite-
   morphism-open-neighborhood] makes each finite over a dense open. They are the required
   alterations.
13. The kernel description in Step 11 proves that $M$ is exactly the schematic closure in $P$ of
   the reduced generic inverse image of $E$, since the generic identifications with $N$ and $D$
   are over $C$. All its claimed finiteness, flatness and finite-presentation properties were
   obtained in Step 10. The generic fibre $P_\eta=N$ is the required normalization and is smooth
   geometrically integral. If $D$ is empty, the kernel of restriction to it is the whole structure
   sheaf, so $M$ is empty; the finite flat and finite-presentation conditions still hold. If $\dim
   Y=0$, normalization and all birational base modifications retain the field base, and the same
   argument specializes to the smooth normalization of the marked generic curve.
-/
theorem exists_equivariant_flat_curve_preparation
    (k : Type u) [Field k] (Y C : Scheme.{u})
    (pY : Y ⟶ Spec (.of k)) (pC : C ⟶ Spec (.of k))
    [IsIntegral Y] [IsIntegral C] [IsHProjective pY] [GeometricallyIntegral pY]
    [LocallyOfFiniteType pC] [QuasiCompact pC]
    (hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (g : C ⟶ Y) [IsProper g] [IsDominant g] (hg : g ≫ pY = pC)
    [GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint Y))]
    (hdim : topologicalKrullDim (g.fiber (genericPoint Y)) = 1)
    (H : Type v) [Group H] [Finite H]
    (σk : H →* (k ≃+* k)) (σC : H →* Aut C) (σY : H →* Aut Y)
    (hC : ∀ h : H, (σC h).hom ≫ pC =
      pC ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (hY : ∀ h : H, (σY h).hom ≫ pY =
      pY ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (heq : ∀ h : H, (σC h).hom ≫ g = g ≫ (σY h).hom)
    (E : Closeds C) (hE : IsNowhereDense (E : Set C))
    (hEstable : ∀ h : H, (σC h).hom '' (E : Set C) = (E : Set C)) :
    ∃ (hgη : g (genericPoint C) = genericPoint Y)
      (_ : Algebra Y.functionField C.functionField),
      algebraMap Y.functionField C.functionField =
        (Y.presheaf.stalkSpecializes (specializes_of_eq hgη) ≫
          g.stalkMap (genericPoint C)).hom ∧
      ∃ (S P : Scheme.{u}) (_ : IsIntegral S) (_ : IsIntegral P)
        (pS : S ⟶ Spec (.of k)) (b : S ⟶ Y) (a : P ⟶ C) (f : P ⟶ S)
        (τS : H →* Aut S) (τP : H →* Aut P),
        IsHProjective pS ∧
        LocallyOfFiniteType (f ≫ pS) ∧ QuasiCompact (f ≫ pS) ∧
        (∀ s : S, IsDomain (S.presheaf.stalk s) ∧
          IsIntegrallyClosed (S.presheaf.stalk s)) ∧
        b ≫ pY = pS ∧ a ≫ pC = f ≫ pS ∧ a ≫ g = f ≫ b ∧
        (∀ h : H, (τS h).hom ≫ pS =
          pS ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom)) ∧
        (∀ h : H, (τP h).hom ≫ f = f ≫ (τS h).hom) ∧
        (∀ h : H, (τS h).hom ≫ b = b ≫ (σY h).hom) ∧
        (∀ h : H, (τP h).hom ≫ a = a ≫ (σC h).hom) ∧
        IsHProjective b ∧ IsProper b ∧ Surjective b ∧ IsDominant b ∧
        IsHProjective a ∧ IsProper a ∧ Surjective a ∧ IsDominant a ∧
        (∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (b ∣_ U)) ∧
        (∃ U : C.Opens, Dense (U : Set C) ∧ IsFinite (a ∣_ U)) ∧
        IsHProjective f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
          ∀ Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) f s), topologicalKrullDim Z = 1) ∧
        ∃ (hbη : b (genericPoint S) = genericPoint Y)
          (_ : Algebra Y.functionField S.functionField),
          algebraMap Y.functionField S.functionField =
            (Y.presheaf.stalkSpecializes (specializes_of_eq hbη) ≫
              b.stalkMap (genericPoint S)).hom ∧
          Module.Finite Y.functionField S.functionField ∧
          IsPurelyInseparable Y.functionField S.functionField ∧
          ∃ (Pη : Scheme.{u}) (_ : IsIntegral Pη) (j : Pη ⟶ P)
            (q : Pη ⟶ Spec S.functionField),
            IsPullback j q f (S.fromSpecStalk (genericPoint S)) ∧
            Smooth q ∧ GeometricallyIntegral q ∧
            (∃ e : Pη ≅ (pullback g (S.fromSpecStalk (genericPoint S) ≫ b)).reducedNormalization,
              e.hom ≫ Scheme.fromReducedNormalization _ ≫
                pullback.fst g (S.fromSpecStalk (genericPoint S) ≫ b) = j ≫ a ∧
              e.hom ≫ Scheme.fromReducedNormalization _ ≫
                pullback.snd g (S.fromSpecStalk (genericPoint S) ≫ b) = q) ∧
            (∃ (hcη : (j ≫ a) (genericPoint Pη) = genericPoint C)
                (_ : Algebra C.functionField Pη.functionField)
                (_ : Algebra S.functionField Pη.functionField),
              algebraMap C.functionField Pη.functionField =
                (C.presheaf.stalkSpecializes (specializes_of_eq hcη) ≫
                  (j ≫ a).stalkMap (genericPoint Pη)).hom ∧
              algebraMap S.functionField Pη.functionField =
                ((Scheme.ΓSpecIso S.functionField).inv ≫ q.appTop ≫
                  Pη.presheaf.Γgerm (genericPoint Pη)).hom ∧
              ∃ e : TensorProduct Y.functionField C.functionField S.functionField ≃+*
                  Pη.functionField,
                ∀ (x : C.functionField) (y : S.functionField),
                  e (TensorProduct.tmul Y.functionField x y) =
                    algebraMap C.functionField Pη.functionField x *
                      algebraMap S.functionField Pη.functionField y) ∧
            ∃ (Dη M : Scheme.{u}) (d : Dη ⟶ Pη) (i : M ⟶ P),
              IsClosedImmersion d ∧ IsReduced Dη ∧
              Set.range d = (j ≫ a) ⁻¹' (E : Set C) ∧
              IsClosedImmersion i ∧ i.ker = (d ≫ j).ker ∧
              (∀ h : H, (τP h).hom '' Set.range i = Set.range i) ∧
              IsFinite (i ≫ f) ∧ Flat (i ≫ f) ∧ LocallyOfFinitePresentation (i ≫ f) ∧
              Etale ((i ≫ f).fiberToSpecResidueField (genericPoint S)) := by
  sorry

end AlgebraicGeometry
