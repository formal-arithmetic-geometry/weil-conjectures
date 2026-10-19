## Worker report

The delivery states `AlgebraicGeometry.Etale.supported_yoneda_localization` in
`Sheaf.AlgebraicGeometry.SupportedYonedaLocalization`, with one real helper definition
`supportedYonedaOpenClosed`, a specialization of the published open-closed short complex.
The sole postponed theorem is the item itself. Its docstring contains all eight proof
steps, including both resolution-extension signs and the final signed coboundary.
No node statement or dependency list is changed; no extra node or dependency repair is needed.

Hypotheses and clauses, with the node and Lean file open:

- A scheme T and closed immersion i:Z→T are `{T Z : Scheme.{u}} (i : Z ⟶ T)
  [IsClosedImmersion i]`. The complementary open is `(W : T.Opens)` with
  `hcomp : Set.range i.base = (Set.range W.ι.base)ᶜ`. Bundling W as an open subscheme
  replaces an arbitrary presentation j by its canonical isomorphic inclusion. This
  neither excludes an open immersion nor chooses a different complement. In particular,
  i may have nonreduced source; only the topological complement is used.
- Arbitrary abelian etale sheaves and their coefficient sequence are `S : ShortComplex
  (Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1})` and `hS : S.ShortExact`, with
  G_a = S.Xₐ. No finiteness, torsion, constructibility, or geometric regularity condition
  occurs. `I : InjectiveResolution S.X₁` is the given nonnegative resolution.
- The ordinary derived Ext group is `CategoryTheory.Abelian.Ext`. Its comparison with
  shifted morphisms in the ordinary derived category is `Ext.homAddEquiv`; composition
  is `Ext.comp`, with `Ext.comp_hom` giving exactly the derived shift in the node.
  No torsion-localized or constructible derived category is substituted.
- The integral open-closed short complex is `supportedYonedaOpenClosed i W hcomp`.
  It calls the recorded `openClosedShortComplex` on the integral constant sheaf
  `constantSheaf ... (AddCommGrpCat.of (ULift.{u+1} ℤ))`. Its last term F is
  `i_* i^* ℤ_T`. `Scheme.upperStarConstantSheafIso` identifies `i^* ℤ_T` canonically
  with ℤ_Z, so this is the same F, with the same adjunction unit p, as the node.
  This uses the published sequence as it is, without introducing a private copy.
- Its exactness proof is the recorded `shortExact_openClosedShortComplex`, instantiated
  on that constant sheaf. The expression `...extClass.comp (Ext.mk₀ a) (add_zero 1)`
  is precisely pushout along a on the first argument of the extension sequence.
  Equivalently it is postcomposition on its coefficient sheaf; `extClass_naturality`
  identifies it with the actual pushout extension. No arbitrary extension class is used.
- The section h is quantified as `h : S.X₃.obj.obj (op (Scheme.Etale.mk W.ι))`.
  The theorem supplies a section t of the first term whose image under the counit is
  `torsorExtensionOne T (Scheme.Etale.mk W.ι)`. The counit is an isomorphism over W,
  so t is unique. It then supplies `a : X₁ ⟶ S.X₃` with `a(t)=h`. By the recorded
  extension-by-zero adjunction and constant-sheaf adjunction, evaluation at this t is
  the bijection Hom(j_!ℤ_W,G₃)=G₃(W). Thus a is exactly the adjoint of 1↦h, rather
  than an uncharacterized map or a new assumption.
- The coefficient class k is `hS.extClass`. The splice is
  `(openClosed.extClass.comp (Ext.mk₀ a) ...).comp hS.extClass (rfl : 1+1=2)`.
  Diagrammatic composition puts e_h first and k second, so `Ext.comp_hom` renders
  k[1]∘e_h, including the canonical identification of successive shifts.
- The theorem supplies an additive equivalence e from Ext²(F,G₁) to the existing
  `relativeCohomology T (Scheme.Etale.mk W.ι) I 2`. For every z:F→I² with dz=0,
  its first conjunct requires `TorsorSignedRepresents ... 1 ((p≫z)(1)) 0
  (e (I.extMk z 3 rfl hz))`. This is exactly the kernel normalization `(z∘p,0)`.
  It fixes the comparison on every class because `I.extMk_surjective` is surjective.
  Existence of this normalized equivalence also includes the supported-Hom comparison
  in this abelian integral specialization. The existing `closedSupportHom` gives the
  general module-valued derived comparison; the present formula fixes its sign in
  the supplied resolution, rather than choosing its unspecified existential iso.
- The target relative group is the node's supported cohomology in its expressly chosen
  signed-fibre model. By the open-closed exact sequence and injectivity of every Iⁿ,
  Hom(F,Iⁿ) is the kernel of Iⁿ(T)→Iⁿ(W), and that restriction is surjective.
  Thus inclusion of the kernel complex in the signed fibre is a quasi-isomorphism;
  the proof docstring records the contractible quotient and contraction. This is
  precisely the derived kernel-of-restriction model of `supportedEtaleSections`,
  with abelian groups as the canonical integral coefficient category. There is no
  need to introduce a second supported-sections functor for abelian groups.
- Ordinary coefficient connecting maps are rendered using all compatible degreewise
  split injective resolution sequences I→J→K. The augmentation equations `_hα`,
  `_hβ` say they resolve the original S; `_hs` says each degree splits. These are
  universally quantified resolution models, not additional geometric hypotheses.
  The prescribed-endpoint horseshoe theorem supplies them for each I, and sections
  preserve their split rows, hence an hOpen exists. `torsorOpenShortComplex` is the
  existing evaluation over W, extended by zero to integer degrees. The input x is
  universally quantified with `TorsorSectionRepresents ... 0 (ε₃(h)) x`; this
  uniquely identifies h in H⁰(W,G₃). The ordinary connecting value δ_W(h) is then
  exactly `hOpen.δ 0 1 rfl x` in the chosen I resolution. This avoids any arbitrary
  cohomology comparison, lift, or stronger existence assumption.
- The right side of the final equality is `torsorLocalizationBoundary ... 1
  (hOpen.δ 0 1 rfl x)`. It is the actual shifted-cone boundary, represented in the
  published signed coordinates by `(0,-b)`. The equality has no negation. It uses
  the ordinary coefficient connecting map; `relativeConnecting` is absent.
- Signed differential and coordinates are the already published `torsorSignedA`,
  `torsorSignedB`, `TorsorSignedRepresents` and `torsorLocalizationBoundary`.
  They use the actual `Cone(r)[-1]`, with signed second coordinate negative of
  the ordinary second coordinate, yielding D(a,b)=(da,res(a)-db).

Dependency declarations read and used (including through public imports):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, supplied for W.ι.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `Sheaf`, with `Scheme.smallEtaleTopology`
  from `Mathlib.AlgebraicGeometry.Sites.Etale` and AddCommGrpCat.{u+1} as recorded.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the ordinary derived-category
  convention; the ordinary Ext encoding actually used is the recorded Mathlib Ext.
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`: `Abelian.Ext`, `Ext.mk₀`,
  `Ext.comp`, `Ext.comp_hom`, `Ext.homAddEquiv`.
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass`:
  `ShortComplex.ShortExact.extClass`, `extClass_naturality`.
- `WeilConjectures.SixFunctors.OpenClosed.Exact`:
  `openClosedShortComplex`, `shortExact_openClosedShortComplex`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `openImmersionLowerShriekUpperStarAdjunction`.
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`: `closedSupportHom` (proof import).
- `Sheaf.AlgebraicGeometry.RelativeEtaleCohomology`: `relativeSections`,
  `relativeSectionComplex`, `relativeCohomology`.
- `Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns`: `torsorExtensionOne`,
  `TorsorSectionRepresents`, `TorsorSignedRepresents`, `torsorOpenShortComplex`,
  `torsorLocalizationBoundary`, `divisor_torsor_boundary_signs`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `InjectiveResolution`;
  `Mathlib.CategoryTheory.Abelian.Injective.Ext`: `extMk`,
  `extAddEquivCohomologyClass`, `extMk_surjective`.
- `Sheaf.AlgebraicGeometry.EtaleSupportedSections`: `supportedEtaleSections`,
  `derivedSupportedEtaleSections` (proof import, no second supported-sections definition).
- `Sheaf.CategoryTheory.FirstResolutionExtensionClass`: `extMk_firstCycles`.
- `WeilConjectures.CategoryTheory.Abelian.HorseshoePrescribedResolutions`:
  `InjectiveResolution.exists_horseshoe_prescribed_resolutions`.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`:
  `Scheme.etaleModule_enoughInjectives`; Mathlib's `InjectiveResolution.of`
  and `instIsIsoToRightDerivedZero'` from the injective-resolution/right-derived API.

Searches (NP / lem-per-supported-yoneda-localization, via prescribed msearch.py):

1. LeanFinder: “Yoneda splice of a coefficient extension and open closed sheaf extension
   equals localization boundary”: eight unrelated representability/sheaf gluing results;
   no matching comparison.
2. Loogle: `CategoryTheory.Abelian.Ext.comp, CategoryTheory.ShortComplex.ShortExact.extClass`:
   twelve hits, including `extClass_naturality`, composition/annihilation and abstract
   Ext exact-sequence identities. These supply the general operations but not this
   normalized signed supported comparison.
3. grep: `extClass|extMk`, subdirectory `CategoryTheory/Abelian/Injective`: five hits
   for extMk and its cocycle/additivity formulas. Read `Injective/Ext.lean`,
   `DerivedCategory/Ext/Basic.lean`, `ExtClass.lean` and the first-resolution sign lemma.
4. LeanSearch: “The Yoneda product of sheaf extensions agrees with localization boundary
   for cohomology with closed support”: eight general sheaf/Yoneda hits, no match.
5. `rg -n 'supported|yoneda|localization'` in upstream WeilConjectures and lean/Sheaf;
   followed by focused `Ext`, `relativeCohomology`, `openClosed`, and filename searches.
   Read ClosedSupportHom, RelativeEtaleCohomology, DivisorTorsorBoundarySigns,
   OrdinarySupportedKummerBoundary and BoundaryExtensionComposition. The Kummer boundary
   is a geometric specialization, not this arbitrary coefficient-sequence comparison.
   `rg` for the item id and the proposed names in upstream and dag/lean_names_upstream.json
   found no existing statement. The helper is a specialization of the existing short
   complex, not a new independent mathematical notion.

Edge cases checked: W empty (only its zero section, zero adjoint and boundary), Z empty
(F=0 and zero supported cohomology), T empty, h=0, split coefficient sequence,
h extending over T (boundary localizes to zero), nonreduced Z, arbitrary nontorsion
G₂ and G₃, and arbitrary nonnegative first resolution I. The signed pair computation
D(x,0)=(dx,res x) gives a positive equality in each case. No hypothesis equates site
object and morphism universes: Scheme.{u}, its standard small etale site, and abelian
groups in Type(u+1) follow the recorded dependency universe convention.

Validation: prescribed scompile.py compiled both sandbox and library-form module cleanly
(5.0 s and 9.8 s); no errors or warnings were reported. All binders and universes are
explicit with autoImplicit false. No data definition contains sorry. No statement fault
or STATEMENT-DISPUTED issue was found.

## Second reading by NP

A fresh in-thread pass read the node statement and completed Lean signature again.
The dispatcher expressly prohibits starting another agent; the maintainer supplies
independent review of this delivery. This paragraph records the worker's own second pass,
not a claim to an independent worker review.

Checked that the complementary-open condition has the direction expected by
shortExact_openClosedShortComplex; F=i_*i^*ℤ_T is canonically the stated i_*ℤ_Z;
the counit generator determines precisely the map adjoint to h; the Ext product is
in the order e_h then k; and e is normalized on every cocycle using `extMk`, without
a sign hidden in the equivalence. Checked the ordinary connecting map is the evaluated
split-resolution δ, and the final localization is the existing cone inclusion, rather
than the relative coefficient connecting map. Universal quantification over compatible
split resolutions keeps the given I arbitrary; the endpoint horseshoe supplies those
models. There is no torsion restriction and no extra geometric assumption. No mismatch
was found in this pass. The extra helper has real data and belongs to this node's
open-closed construction; no missing independent notion was introduced.
