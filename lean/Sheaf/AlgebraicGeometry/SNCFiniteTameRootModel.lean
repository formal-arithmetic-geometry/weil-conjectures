module

public import Sheaf.AlgebraicGeometry.SNCTameRootEtaleExtension
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantSetsDescent
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback
import Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk
import Sheaf.AlgebraicGeometry.SNCBoundaryParameterCriterion
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Yoneda

/-! # Finite tame sheaves at a finite parameter-root level

Source: ILO, Travaux de Gabber, IX Proposition 2.1(i)--(iii), pp.133--134;
Bhatt--Scholze, Lemmas 5.1.2 and 5.1.4, p.34.
(blueprint: lem-sfb-snc-finite-tame-root-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SNCTameExtension

/-- The canonical scalar extension of the finite root level to Spec H. Its source
is canonically Spec (H tensor_B B_n); the arrow is its projection to Spec B_n.
Source: ILO IX 2.1, scalar extension of the finite root model
(blueprint: lem-sfb-snc-finite-tame-root-model). -/
abbrev scalarRootProjection {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B)
    (n : ℕ) (H : Type u) [CommRing H] [Algebra B H] :=
  pullback.fst (finiteProjection t n) (Spec.map (CommRingCat.ofHom (algebraMap B H)))

/-- Restrict the scalar-extended root level to the boundary complement. Its source
is canonically Spec H_n[1/f], and this arrow maps it to Spec H_n.
Source: ILO IX 2.1, puncturing after scalar extension
(blueprint: lem-sfb-snc-finite-tame-root-model). -/
abbrev scalarRootOpen {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B)
    (n : ℕ) (H : Type u) [CommRing H] [Algebra B H] :=
  pullback.snd (puncture t) (scalarRootProjection t n H ≫ finiteProjection t n)

/-- The same punctured scalar root level, mapped to the original boundary complement.
Source: ILO IX 2.1, the structural map for inverse image of F_0
(blueprint: lem-sfb-snc-finite-tame-root-model). -/
abbrev scalarRootToOpen {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B)
    (n : ℕ) (H : Type u) [CommRing H] [Algebra B H] :=
  pullback.fst (puncture t) (scalarRootProjection t n H ≫ finiteProjection t n)

/-- A finite locally constant tame set sheaf is represented by a finite etale cover,
and that cover extends at a finite prime-to-p root level, compatibly with arbitrary
scalar extension. The representation identifies maps by Yoneda and fibres by evaluation.
The labelled branch equations define precisely the distinct reduced components.
Source: ILO IX 2.1(i)--(iii), printed pp.133--134; Bhatt--Scholze 5.1.2 and 5.1.4.
(blueprint: lem-sfb-snc-finite-tame-root-model).

Proof (the stage-1 finite-frame argument and finite-root extension):
1. Write $X=V^\circ$. For $d\geq0$ let $T_d=\operatorname{Isom}(\underline{\{1,\ldots,d\}},F_0)$
   on $X_{\mathrm{proet}}$; isomorphisms glue uniquely, so $T_d$ is a sheaf. On a trivializing
   member $U$ with model a finite set $S$, a map $\underline{\{1,\ldots,d\}}\to F_0$ is $d$
   sections, since a finite constant sheaf is the coproduct of $d$ copies of the final sheaf;
   after a common covering refinement these sections and the inverse images are constant, and
   the inverse equations are exactly those of a bijection. Thus $T_d|_U$ is the constant sheaf
   of the finite set of bijections $\{1,\ldots,d\}\to S$, empty unless $d=|S|$ and a singleton
   for $d=|S|=0$. So each $T_d$ is locally constant, hence $T_d\simeq\nu_X^*H_d$ for an etale
   set sheaf $H_d$ by local classicality. Let $T=\coprod_dT_d$ (sheaf coproduct). As $\nu_X^*$
   is a left adjoint, $T\simeq\nu_X^*H$ with $H=\coprod_dH_d$, compatibly with the summand
   inclusions. $T$ restricts on $U$ to the constant sheaf of the nonempty set of orderings of
   $S$, so $T$ is locally classical with sections on a pro-etale covering, and the sections
   clause gives an etale covering $\{Y_i\to X\}$ with $T(Y_i)\neq\varnothing$. For etale $Y$,
   $\nu_{X,*}$ is evaluation at $Y$, so the comparison unit gives $H(Y)\simeq T(Y)$ and
   $H_d(Y)\simeq T_d(Y)$, naturally in $Y$ and compatibly with the inclusions $H_d\to H$. A
   section of the etale sheaf coproduct $H$ over $Y_i$ lies, on an etale covering $\{Y'\to
   Y_i\}$, in single summands $H_d(Y')$: sheafification is locally surjective, because the
   subsheaf of locally-presheaf sections receives the presheaf map, and the universal property
   makes it everything. Hence $T_d(Y')\neq\varnothing$, i.e.
   $F_0|_{Y'}\simeq\underline{\{1,\ldots,d\}}$ on these etale members $Y'$. So $F_0$ has finite
   constant models on an etale covering of $X$.
   Uses: lem-weil-pbc-proetale-locally-classical-etale-cover, lem-weil-pbc-proetale-comparison-
   unit-sets, def-weil-pbc-site-comparison-morphism, def-weil-pbc-sheafification.
2. Apply local classicality also to $F_0$ itself, obtaining $F_0\simeq\nu_X^*G$ for an etale set
   sheaf $G$. On each etale trivializing member $U$ of step 1, comparison and restriction
   commute: both right adjoints evaluate a sheaf at the same etale $U$-scheme, hence their left
   adjoints agree. Constants are inverse images from sets and are preserved by these left
   adjoints. Full faithfulness of $\nu_U^*$ therefore identifies $G|_U$ with the finite constant
   model of $F_0|_U$. Apply finite-locally-constant sets descent to $G$: it supplies a finite
   etale $P\to X$ and $G\simeq h_P$.
   Uses: lem-weil-pbc-proetale-locally-classical-etale-cover, lem-weil-pbc-proetale-comparison-
   unit-sets, def-weil-pbc-site-comparison-morphism, lem-weil-pbc-finite-locally-constant-sets-
   descent.
3. The inclusion of the etale site in the pro-etale site preserves finite limits and coverings.
   Both sites are subcanonical. Apply representable inverse image to this inclusion:
   $\nu_X^*h_P\simeq h_P$ on the pro-etale site, so step 2 represents $F_0$ there. Yoneda
   identifies all maps between these represented sheaves with $X$-morphisms between their finite
   etale schemes. At a geometric point, the comparison-stalk isomorphism reduces the fibre
   assertion to $G$. On the etale splitting cover of step 1 both the stalk of $G$ and the
   geometric fibre of $P$ are the same finite set of labels; evaluation of a section at the
   point is this identification. These local identifications agree on overlaps because
   evaluation commutes with restriction, giving the asserted natural fibre identification.
   Uses: def-weil-pbc-site-comparison-morphism, lem-weil-pbc-small-etale-representable-presheaf-
   sheaf, lem-weil-pbc-proetale-subcanonical, lem-pur-site-representable-algebraic-pullback,
   lem-galois-yoneda-hom-bijection, lem-cbc-proetale-comparison-stalk.
4. Fix $v\in V$. The SNC parameter criterion gives parameters $u_1,\ldots,u_d$ in $A=\mathcal
   O_{V,v}$ with boundary ideal $(u_1\cdots u_s)$. The regular-local factorization lemma says
   that these $u_j$ are distinct prime elements. Since the $t_i$ are equations of the labelled
   reduced branches, the principal ideals $(t_i)$ for the vanishing labels are precisely the
   distinct minimal primes $(u_j)$ of this product ideal: in a domain a prime containing a
   product contains a factor. Equality of nonzero principal ideals in a domain gives $t_i=a_i
   u_{\sigma(i)}$ for units $a_i$. Replacing the corresponding parameters by these unit
   multiples preserves generation of the maximal ideal and its number of generators. It follows
   from the definition of a regular system of parameters that the vanishing $t_i$ extend to one.
   Off the boundary the list is empty.
   Uses: lem-sfb-snc-boundary-parameter-criterion, lem-trf-regular-local-ufd-boundary-
   factorization, def-weil-pbc-regular-system-of-parameters.
5. For any scheme map $a:T\to X$ and finite etale $Q\to X$, the pro-etale inverse image of $h_Q$
   is $h_{Q\times_XT}$: apply the representable inverse-image theorem to the base-change functor
   defining $a^{-1}$. Its finite-limit and covering conditions are precisely those recorded in
   the inverse-image definition, and subcanonicality holds for both pro-etale sites. In
   particular apply this to each punctured strict-local full parameter-root tower. The
   hypothesis says that the resulting represented sheaf is finite constant. A finite constant
   sheaf is a finite coproduct of final sheaves; the finite-coproduct comparison identifies it
   with the sheaf represented by the corresponding finite disjoint union of the tower. Yoneda
   turns this isomorphism into a scheme isomorphism. Consequently the pullback of $P$ to every
   one of the towers in the root-extension lemma is a finite disjoint union of copies of that
   tower.
   Uses: def-weil-proetale-inverse-image, lem-pur-site-representable-algebraic-pullback, lem-
   weil-pbc-proetale-subcanonical, lem-weil-pbc-proetale-qcqs-finite-family-geometry, lem-
   galois-yoneda-hom-bijection.
6. Apply the SNC tame root-extension lemma to $V$, the given labelled equations, and $P$. The
   regularity, Noetherianity, separated finite type over $k$, and positive characteristic
   hypotheses are those of the item. Step 4 verifies its parameter hypothesis, and step 5
   verifies its exact tower-splitting hypothesis, with the same active labels and power
   transition maps. It gives $n>0$ prime to $p$ and finite etale $Z\to\operatorname{Spec}B_n$,
   together with $Z[1/f]\simeq P\times_X\operatorname{Spec}B_n[1/f]$. No degree condition is
   used by that lemma.
   Uses: lem-sfb-snc-tame-root-etale-extension.
7. For an arbitrary $B$-algebra $H$, base change of $Z$ is finite by finite-morphism permanence
   and etale by etale base change. Therefore $E_n\to\operatorname{Spec}H_n$ is finite etale.
   Pull the isomorphism of step 6 back to $\operatorname{Spec}H_n[1/f]$. Associativity of fibre
   products, or its two projection equations, identifies its right side with
   $P\times_X\operatorname{Spec}H_n[1/f]$. The representable inverse-image comparison identifies
   the sheaf of this last scheme with the pullback of $F_0$. Thus it is the restriction
   $E_n[1/f]$ that represents this sheaf. Nothing here requires $H$ to be Noetherian or flat.
   Uses: lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-etale-scheme-base-change, def-
   weil-proetale-inverse-image, lem-pur-site-representable-algebraic-pullback, lem-weil-pbc-
   proetale-subcanonical.
8. If $r=0$, then $f=1$, $B_n=B$, and $n=1$, $Z=P$ work. If $F_0$ is empty, use $P=\varnothing$,
   $n=1$, $Z=\varnothing$; the frame of its empty fibre remains the unique empty ordering, so
   the descent argument includes it. If $V$ is empty all constructions are the unique empty
   covers. Arbitrary finite fibre cardinalities and disconnected schemes were allowed
   throughout, and no step requires the degree of $P$ to be prime to $p$.
-/
theorem exists_finite_tame_root_model
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (B : Type u) [CommRing B] (b : Spec (.of B) ⟶ Spec (.of k))
    [LocallyOfFiniteType b] [QuasiCompact b] [IsSeparated b]
    (_hB : IsRegularScheme (Spec (.of B)))
    (r : ℕ) (t : Fin r → B) (D : (Spec (.of B)).IdealSheafData)
    (_hD : IsStrictNormalCrossingsBoundary D)
    (_hproduct : D = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of B)).inv (∏ i, t i)}))
    (_hreduced : ∀ i, _root_.IsReduced (B ⧸ Ideal.span ({t i} : Set B)))
    (_hdistinct : Function.Injective (fun i ↦ PrimeSpectrum.zeroLocus ({t i} : Set B)))
    (_hbranches : Set.range (fun i ↦ PrimeSpectrum.zeroLocus ({t i} : Set B)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (D.support : Set (Spec (.of B)))))
    (F₀ : Sheaf (Scheme.ProEt.topology (Spec (.of (Localization.Away (∏ i, t i)))))
      (Type (u + 1)))
    (_hlocal : ∃ (I : Type (u + 1))
      (U : I → (Spec (.of (Localization.Away (∏ i, t i)))).ProEt),
      (Scheme.ProEt.topology _).CoversTop U ∧ ∀ i,
        ∃ S : Type (u + 1), Finite S ∧ Nonempty
          ((Scheme.proEtaleSetRestriction _ (U i)).obj F₀ ≅
            (constantSheaf (Scheme.ProEt.topology (U i).left) (Type (u + 1))).obj S))
    (_htame : ∀ (q : PrimeSpectrum B) (K H : Type u) [Field K]
      [Algebra (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) K]
      [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) K]
      [Algebra (Localization.AtPrime q.asIdeal) K]
      [IsScalarTower (Localization.AtPrime q.asIdeal)
        (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) K]
      [CommRing H] [Algebra (Localization.AtPrime q.asIdeal) H],
      Algebra.StrictHenselizationPresentationIn (Localization.AtPrime q.asIdeal) K H →
        ∃ S : Type (u + 1), Finite S ∧ Nonempty
          ((Scheme.proEtaleSheafInverseImage (localPuncture p t q H) (Type (u + 1))).obj F₀ ≅
            (constantSheaf (Scheme.ProEt.topology _) (Type (u + 1))).obj S)) :
    (∀ q : PrimeSpectrum B,
      ∃ (_hnoeth : IsNoetherianRing (Localization.AtPrime q.asIdeal))
        (s : List (Localization.AtPrime q.asIdeal)),
        IsLocalRing.IsRegularSystemOfParameters s ∧
          ((active t q).map (algebraMap B (Localization.AtPrime q.asIdeal))).Sublist s) ∧
    ∃ (P : Scheme.{u}) (π : P ⟶ Spec (.of (Localization.Away (∏ i, t i))))
      (_hfinite : IsFinite π) (_hetale : Etale π),
      ∃ eP : F₀.obj ≅ uliftYoneda.{u + 1}.obj (Scheme.ProEt.mk π),
        (∀ (Q : Scheme.{u}) (ρ : Q ⟶ Spec (.of (Localization.Away (∏ i, t i))))
          [IsFinite ρ] [Etale ρ]
          (G : Sheaf (Scheme.ProEt.topology _) (Type (u + 1)))
          (eQ : G.obj ≅ uliftYoneda.{u + 1}.obj (Scheme.ProEt.mk ρ)) (η : F₀ ⟶ G),
          ∃! g : Scheme.ProEt.mk π ⟶ Scheme.ProEt.mk ρ,
            η.hom ≫ eQ.hom = eP.hom ≫ uliftYoneda.{u + 1}.map g) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (y : Spec (.of Ω) ⟶ Spec (.of (Localization.Away (∏ i, t i)))),
          ∃ e : Scheme.proEtaleGeometricSetStalk y F₀ ≅
            ULift.{u + 1} (Over.mk y ⟶ Over.mk π),
            ∀ (N : Scheme.ProEtaleGeometricNeighbourhood y)
              (s : F₀.obj.obj (op N.right)),
              (e.hom ((colimit.ι (Scheme.proEtaleGeometricStalkDiagram y F₀) (op N)) s)).down =
                N.hom ≫ (Scheme.ProEt.forget _).map ((eP.hom.app (op N.right) s).down)) ∧
        ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧
          ∃ (Z : Scheme.{u}) (ζ : Z ⟶ Spec (.of (MvPolynomial (Fin r) B ⧸
            Ideal.span (Set.range (fun i ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))))),
            IsFinite ζ ∧ Etale ζ ∧
            (∃ e : pullback ζ (pullback.snd (puncture t) (finiteProjection t n)) ≅
                pullback π (pullback.fst (puncture t) (finiteProjection t n)),
              e.hom ≫ pullback.snd _ _ = pullback.snd _ _) ∧
            ∀ (H : Type u) [CommRing H] [Algebra B H],
              IsFinite (pullback.snd ζ (scalarRootProjection t n H)) ∧
              Etale (pullback.snd ζ (scalarRootProjection t n H)) ∧
              ∃ h : WeaklyEtale
                (pullback.snd (pullback.snd ζ (scalarRootProjection t n H))
                  (scalarRootOpen t n H)),
                Nonempty
                  (((Scheme.proEtaleSheafInverseImage (scalarRootToOpen t n H)
                    (Type (u + 1))).obj F₀).obj ≅
                    uliftYoneda.{u + 1}.obj
                      (@Scheme.ProEt.mk _ _
                        (pullback.snd (pullback.snd ζ (scalarRootProjection t n H))
                          (scalarRootOpen t n H)) h)) := by
  sorry

end AlgebraicGeometry.ProEtale.SNCTameExtension
