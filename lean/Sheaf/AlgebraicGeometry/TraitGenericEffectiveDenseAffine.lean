module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.MorphismProperty.Descent
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact
import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import WeilConjectures.AlgebraicGeometry.InvariantOpenEffectiveDescent
import WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend
import Sheaf.AlgebraicGeometry.Morphisms.FpqcOpenImmersionDescent

/-! # An invariant dense affine open from generic effectivity over a trait

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §6.5, proof of Theorem 1,
pp.160--162, and §6.4 Lemma 4.
(blueprint: lem-sfb-trait-generic-effective-dense-affine)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Generic effectivity over a faithfully flat extension of discrete valuation rings gives an
invariant affine open dense in every geometric fibre, with the prescribed generic embedding.

Source: BLR, Néron Models, §6.5 Theorem 1 proof, pp.160--162, using §6.4 Lemma 4.
(blueprint: lem-sfb-trait-generic-effective-dense-affine)

The fraction-field map `s` is characterized by `hs`. The supplied isomorphism `e₀` is over
`Spec (.of L)` by `he₀`. Its compatibility with the generic restriction of `D` is `hgeneric`:
whenever two points are related by transport and lift to the generic fibre, their images
in `X₀` agree. The lifts are unique because the generic-point map is a monomorphism.
The conclusion expresses invariance by equality of inverse-image opens under the universal
transport and the first projection. The cartesian square for `q`, together with transport
invariance of `q`, is precisely an effective realization of the restricted datum, equivalently
an isomorphism `U ×_S S' ≅ W` realizing it. The last universal equation identifies the base
change of `i` with the original generic inclusion through the specified `e₀`. All maps in
that equation are constrained by their fibre-product projections; they are not arbitrary
comparison maps. No nonemptiness assumption or group structure occurs.

Proof:
1. The affine map p:S'\to S is flat and surjective by the affine flatness criterion and
   faithful-flat spectrum surjectivity; it is quasi-compact by affine-morphism permanence, hence
   is a singleton fpqc covering. The DVR definition makes B,C principal ideal domains, hence
   Noetherian normal domains of dimension one. Smooth-trait infrastructure makes X' Noetherian
   and regular with finitely many pairwise disjoint special-fibre components and schematically
   dense generic fibre. Its open subschemes remain Noetherian; their inclusions are
   quasi-compact and of finite type, and they remain smooth by smooth open restriction.
   Separatedness of any such open over S' follows directly by restricting the closed diagonal of
   X'/S'. These observations justify all later applications to open subschemes. A uniformizer of
   B maps to a unit times a positive power of a uniformizer of C: surjectivity on spectra forces
   the closed point to map to the closed point. Thus C\otimes_B K=L.
2. The scheme X_0 is smooth, separated and of finite type over K: its pullback along the fpqc
   field extension L/K is X'_L, which has those properties by base change. Apply fpqc descent of
   smoothness, separatedness, local finite type and quasi-compactness. A field is Noetherian
   (its only ideals are zero and the whole ring); hence X_0 is Noetherian and has finitely many
   irreducible components. The dense affine-cover existence statement supplies an affine open
   V_0\subseteq X_0 containing every component generic point, so V_0 is dense. Density persists
   under extension to L by smooth fibrewise-density base change. If X_0 is empty then schematic
   density of the generic fibre forces X' empty; take U=U'=\varnothing. Henceforth allow
   nonempty X_0 and choose V_0 as above.
3. Take the reduced induced closed complement Z_0=(X_0\setminus V_0)_{\mathrm{red}}, set
   Z_L=(Z_0)_L in X'_L, and let Z' be its schematic closure in X'. We retain this base-changed
   closed subscheme structure, rather than reducing after scalar extension; it is therefore
   preserved by the specified generic datum even for inseparable L/K. The horizontal-closure
   lemma shows that Y'=X'\setminus |Z'| is dense in every geometric fibre and has affine generic
   fibre (V_0)_L. It is invariant: the generic datum preserves Z_L as a closed subscheme, and
   schematic image commutes with flat pullback to either projection S'\times_S S'\to S'. These
   projections are flat by fpqc base change. The immersion defining the closure is
   quasi-compact, since X'_L\to X' is the principal open defined by a base uniformizer and Z_L
   is closed in it. Hence the cited flat schematic-image theorem applies even if the double
   overlap is non-Noetherian. Complements of the identified pulled-back closed subschemes agree,
   giving the restricted datum on Y'.
4. For any invariant open Y\subseteq Y' whose generic fibre is (V_0)_L, form
   A_Y=\Gamma(Y,\mathcal O_Y) and its canonical affinization a_Y:Y\to\operatorname{Spec}A_Y.
   Flat base change of global sections identifies both pulled-back affine targets over the
   double overlap with the spectra of the corresponding section rings. The isomorphism of the
   two pulled-back copies of Y therefore induces an isomorphism of these targets, intertwining
   the two maps a_Y: their section maps both send a pure tensor b\otimes r to the product of the
   pulled-back sections b,r. Functoriality gives the cocycle. The affinization-locus lemma gives
   a quasi-compact quasi-affine open W(Y) containing the whole generic fibre, and meeting the
   special fibre whenever Y does. By the cited base-change compatibility of the quasi-finite
   locus, its pullbacks agree under the datum. Thus W(Y) is invariant and its datum is effective
   by quasi-affine fpqc effectivity. No finite generation of A_Y is assumed.
5. For a smooth finite-type field scheme F and an open O, its irreducible components are
   finitely many and pairwise disjoint open-and-closed subsets, by geometric normality and
   normal Noetherian component decomposition. Hence the union H_F(O) of those meeting O is open
   and closed. On each such component D, the nonempty open O\cap D is dense; smooth
   fibrewise-density base change makes its pullback dense in D_{k'} for every field extension
   k'/k, so it meets every component upstairs. Components disjoint from O remain disjoint after
   pullback. Thus H_F(O) commutes with field extension. For invariant W(Y)\subseteq Y, test this
   equality over residue fields of points of S'\times_S S': the datum identifies the two copies
   of W(Y), so identifies their component saturations on the closed fibres. Equality on all
   these point sets is equality of open-and-closed fibre subsets. Their complements in the two
   copies of Y are consequently invariant open subschemes. This is a direct three-part argument
   from the cited statements, requiring no new component-saturation node.
6. Set Y_0=Y' and, as long as (Y_i)_k is nonempty, put W_i=W(Y_i), let H_i be the union of the
   special-fibre components of Y_i meeting W_i, and set Y_{i+1}=Y_i\setminus H_i. Here H_i is
   closed in the special fibre and therefore in Y_i; its complement is open and invariant by
   step 5. No generic point is removed, so (Y_{i+1})_L=(V_0)_L remains affine and step 4 applies
   again. The special-fibre components are disjoint. Since (W_i)_k is nonempty, at least one
   previously remaining component is removed, and none of the others changes. Induction on the
   finite number of special-fibre components therefore terminates. Include also the last
   W(Y_N)=Y_N when its special fibre is empty; its whole scheme is its affine generic fibre. Let
   V'=\bigcup_{i=0}^N W_i. It is invariant, contains (V_0)_L, and meets every component of Y'_k
   in a nonempty open. It is dense in that fibre, and step 5's field-extension argument makes
   this density geometric. Since Y' was fibrewise geometrically dense in X', so is V'. All opens
   here are finite type and smooth by step 1. When Y'_k is empty this construction consists just
   of W(Y')=Y'.
7. Each W_i has effective restricted datum by step 4. Apply effective descent gluing on the
   invariant open cover (W_i) of V' to obtain a scheme V over S and a compatible isomorphism
   V\times_S S'\simeq V'. The scheme V is smooth, separated and of finite type by the same four
   fpqc descent statements used in step 2. Its generic fibre has an open immersion into X_0:
   descend the compatible inclusion V'_L=(V_0)_L\hookrightarrow X'_L along L/K by fpqc morphism
   descent, then apply fpqc descent of open immersions. This uses morphism descent only after
   both schemes exist. The resulting morphism identifies V_K with V_0 and realizes the specified
   generic identification.
8. Apply the Dedekind smooth fibre-dense affine lemma to V\to\operatorname{Spec}B, using that B
   is Noetherian, integrally closed and of dimension one from step 1. It gives an affine open
   U\subseteq V dense in every geometric fibre. Its pullback U'=U\times_S S' is an invariant
   open of V', hence of X', with the prescribed effective isomorphism. It is affine because base
   change preserves affine morphisms and the base S' is affine. Smooth fibrewise-density base
   change makes U' fibrewise dense in V'. Composing dense open inclusions with V'\subseteq X'
   gives density in every geometric fibre of X'. Finally the inclusion U_K\subseteq V_K followed
   by the open immersion V_K\hookrightarrow X_0 is the requested open immersion; its base change
   is the original inclusion in X'_L by its construction in step 7. The argument permits empty
   special fibres and the empty scheme.
-/
theorem trait_generic_effective_dense_affine
    (B C K L : Type u) [CommRing B] [CommRing C]
    [IsDomain B] [IsDiscreteValuationRing B] [IsDomain C] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Algebra B K] [IsFractionRing B K]
    [Algebra C L] [IsFractionRing C L]
    (r : CommRingCat.of B ⟶ CommRingCat.of C) (hr : r.hom.FaithfullyFlat)
    (s : CommRingCat.of K ⟶ CommRingCat.of L)
    (hs : s.hom.comp (algebraMap B K) = (algebraMap C L).comp r.hom)
    (X : Over (Spec (.of C))) [Smooth X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (D : Over.DescentDatum (Spec.map r) X) (X₀ : Over (Spec (.of K)))
    (e₀ : pullback X₀.hom (Spec.map s) ≅
      pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap C L))))
    (he₀ : e₀.hom ≫ pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap C L))) = pullback.snd X₀.hom (Spec.map s))
    (hgeneric : ∀ (T : Scheme.{u}) (f₁ f₂ : T ⟶ Spec (.of C))
      (h : f₁ ≫ Spec.map r = f₂ ≫ Spec.map r)
      (a : Over.mk f₁ ⟶ X) (b : Over.mk f₂ ⟶ X)
      (aL bL : T ⟶ pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap C L)))),
      D.transport f₁ f₂ h a = b →
      aL ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap C L))) = a.left →
      bL ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap C L))) = b.left →
      aL ≫ e₀.inv ≫ pullback.fst X₀.hom (Spec.map s) =
        bL ≫ e₀.inv ≫ pullback.fst X₀.hom (Spec.map s)) :
    ∃ (U : Over (Spec (.of B))) (W : X.left.Opens),
      IsAffine U.left ∧ IsAffine W.toScheme ∧
      (pullback.fst (X.hom ≫ Spec.map r) (Spec.map r)) ⁻¹ᵁ W = D.toHom ⁻¹ᵁ W ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of C)),
        Dense ((pullback.fst X.hom g) ⁻¹' (W : Set X.left))) ∧
      ∃ q : W.toScheme ⟶ U.left,
        IsPullback q (W.ι ≫ X.hom) U.hom (Spec.map r) ∧
        (∀ (T : Scheme.{u}) (f₁ f₂ : T ⟶ Spec (.of C))
          (h : f₁ ≫ Spec.map r = f₂ ≫ Spec.map r)
          (a : Over.mk f₁ ⟶ X) (b : Over.mk f₂ ⟶ X) (aW bW : T ⟶ W.toScheme),
          D.transport f₁ f₂ h a = b → aW ≫ W.ι = a.left → bW ≫ W.ι = b.left →
          aW ≫ q = bW ≫ q) ∧
        ∃ i : pullback U.hom (Spec.map (CommRingCat.ofHom (algebraMap B K))) ⟶ X₀.left,
          IsOpenImmersion i ∧
          i ≫ X₀.hom = pullback.snd U.hom
            (Spec.map (CommRingCat.ofHom (algebraMap B K))) ∧
          ∀ (T : Scheme.{u})
            (aL : T ⟶ pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap C L))))
            (aW : T ⟶ W.toScheme)
            (b : T ⟶ pullback U.hom (Spec.map (CommRingCat.ofHom (algebraMap B K)))),
            aL ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap C L))) =
              aW ≫ W.ι →
            b ≫ pullback.fst U.hom (Spec.map (CommRingCat.ofHom (algebraMap B K))) =
              aW ≫ q →
            b ≫ pullback.snd U.hom (Spec.map (CommRingCat.ofHom (algebraMap B K))) =
              aL ≫ pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap C L))) ≫
                Spec.map s →
            b ≫ i = aL ≫ e₀.inv ≫ pullback.fst X₀.hom (Spec.map s) := by
  sorry

end AlgebraicGeometry
