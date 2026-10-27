## Worker report

The module `Sheaf.CategoryTheory.NormalizedComparisonAugmentedResolution` states
`CategoryTheory.normalizedComparison_augmentedResolution` and
`CategoryTheory.augmentedResolutionComputation_naturality`. These are equalities
of morphisms in `DerivedCategory.Plus D`, not equalities only after cohomology.
The node's natural-language statement and all dependency lists are unchanged.
Only its `lean` field is filled.

The same module supplies three small constructions belonging to this node:
`augmentedResolutionSingle` bundles the existing Mathlib single complex as a
bounded-below complex; `augmentedResolutionComputation` constructs the specified
computation **isomorphism** from the given augmentation and comparison unit;
`augmentedResolutionTransport` constructs exactly the isomorphism called e.
All their data are actual constructions. The additional named theorem
`augmentedResolution_isIso_Q_map` is the localization inverse-existence assertion
in the node's proof step 1; its postponed proof is documented. Every helper is
listed in `lean.declarations` and carries this node's source and blueprint tag.
There are no new independent notions, new nodes, or dependency repairs.

Clause-by-clause correspondence (Lean composition `≫` is left-to-right):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Abelian A, B, D | Explicit type and `Category` binders, then `[Abelian A]`, `[Abelian B]`, `[Abelian D]`. |
| A and B have enough injectives | `[EnoughInjectives A] [EnoughInjectives B]`; no such condition on D. |
| Bounded-below complexes and their localization | `CochainComplex.Plus`, `HomotopyCategory.Plus`, `DerivedCategory.Plus.Q` and `DerivedCategory.Plus.Qh`. The complex localization is the quotient followed by the homotopy localization. |
| Chosen derived categories and all sizes | Independent object, morphism, and localization universes `uA vA wA`, `uB vB wB`, `uD vD wD`, with `[HasDerivedCategory.{wA} A]` and analogues. |
| Additive U, E, H | `(U : B ⥤ A) (E : A ⥤ D) (H : B ⥤ D)` and the three `Additive` instances. There is no left-exactness assumption. |
| Fixed RU, RE, RH and natural comparisons | Functor parameters `RU`, `RE`, `RH`, natural-transformation parameters `αU`, `αE`, `αH`, and their three `IsRightDerivedFunctor` instances. These are arbitrary fixed derived pairs, not replaced by selected canonical ones. |
| Canonical computation on injective complexes | Mathlib's instance from `DerivedCategory.DerivabilityStructureInjectives` makes each comparison component invertible on termwise injectives. `asIso` uses that exact comparison component. |
| Underived natural isomorphism sigma | `(σ : U ⋙ E ≅ H)`. `Functor.mapHomotopyCategoryPlusCompIso σ` applies this exact isomorphism termwise and passes to homotopy classes. |
| Given normalized derived isomorphism b | `(b : RU ⋙ RE ≅ RH)`. `hb` quantifies over every bounded-below homotopy complex K with both K and UK termwise injective and states `αE ≫ RE.map αU ≫ b = Qh.map σ ≫ αH`. |
| M, N and the chosen injective resolution h | `(M : A) (N : B) (J : CochainComplex.Plus B)`, termwise `Injective` instances, `h : N[0] ⟶ J`, and `[QuasiIso h.hom]`. The single complex is `augmentedResolutionSingle`. This allows arbitrary integer lower bounds, without restricting J to a particular nonnegative resolution. |
| I = UJ termwise injective and augmentation a | I is written everywhere as `U.mapCochainComplexPlus.obj J`, with its termwise `Injective` binder; `a : M[0] ⟶ I` has `[QuasiIso a.hom]`. No arbitrary I or identification is introduced. |
| e = RU(Qh)^(-1) alphaU | `augmentedResolutionTransport U RU αU N J h` is the composite `asIso αU ≪≫ (RU.mapIso (asIso (Q.map h))).symm`. |
| eta = e Qa | In the main theorem, `DerivedCategory.Plus.Q.map a ≫ (augmentedResolutionTransport ...).hom`. Both factors are invertible. |
| cE and cH, with exactly a and h | `augmentedResolutionComputation E RE αE M I a` and `augmentedResolutionComputation H RH αH N J h`; the definition is `asIso (RE.map (Q.map a)) ≪≫ (asIso αE).symm`, and similarly for H. |
| Specified c = b RE(eta) | The left side begins `RE.map (Q.map a ≫ e.hom) ≫ b.hom.app (Q.obj N[0])`. |
| cH c = Q(sigmaJ) cE | The main conclusion is exactly `RE.map eta ≫ b.hom.app ... ≫ cH.hom = cE.hom ≫ Qh.map (sigmaJ)`. The termwise sigma is the image under the bounded homotopy quotient of the chain isomorphism, so this is the required Q(sigmaJ). |
| Chain representative sigmaJ and identity specialization | The preceding equality uses the precise chosen computation isomorphisms on both sides, so it specifies the representative. Taking `H = U ⋙ E` and `σ = Iso.refl _` specializes this very equality to the identity representative; the composite-to-termwise identification is the canonical one, not arbitrary comparison data. No per-degree weakening is made. |
| Maps f, g, t of augmented data | The naturality theorem binds primed and unprimed copies of every object, augmentation, quasi-isomorphism and injectivity assumption, then `(f : M ⟶ M') (g : N ⟶ N') (t : J ⟶ J')`. |
| th = h'g and U(t)a = a'f | Binders `ht : h ≫ t = single.map g ≫ h'` and `ha : a ≫ U.mapCochainComplexPlus.map t = single.map f ≫ a'`. These are actual chain-map equalities, before localization. |
| E computation naturality | The first conjunct is `RE.map (Q.map (single.map f)) ≫ cE'.hom = cE.hom ≫ Q.map (E.mapCochainComplexPlus.map (U.mapCochainComplexPlus.map t))`. |
| H computation naturality | The second conjunct is `RH.map (Q.map (single.map g)) ≫ cH'.hom = cH.hom ≫ Q.map (H.mapCochainComplexPlus.map t)`. |
| sigma naturality | The third conjunct is `Q(sigmaJ) ≫ Q(H(t)) = Q(EU(t)) ≫ Q(sigmaJ')`. This has precisely the same order as the node's right-to-left notation. |

Dependencies read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-pbc-bounded-derived-subcategories`: `DerivedCategory.Plus`,
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`; `Qh` and `Q` are in
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`.
- `def-sp-left-exact-additive`: its recorded additive clause is
  `CategoryTheory.Functor.Additive`,
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`. Its per-degree
  `rightDerived` construction is not substituted for the D⁺-valued functors.
- `lem-weil-pbc-right-derived-plus-injective`: the recorded Mathlib interface in
  `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus` and
  `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`,
  together with `CategoryTheory.Functor.IsRightDerivedFunctor` from
  `Mathlib.CategoryTheory.Functor.Derived.RightDerived`. In particular, the
  instance at the recorded injective-computation clause is used to build the
  computation isomorphisms for the given α, not only for a preferred derived pair.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, and the read
  `CategoryTheory.InjectiveResolution` interface in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`. The arbitrary
  integer-indexed resolution named in this node is rendered directly by the same
  injectivity and quasi-isomorphism conditions, rather than forcing it into the
  separate natural-number-indexed bundled resolution.

The first public import exposes the derived-category, boundedness, abelian,
additive-functor and injective-computation dependency modules transitively; the
second exposes the recorded injective-resolution module. The proof dependencies
are the same Mathlib localization and injective-computation interfaces already
publicly needed by the statement. There is no omitted import due to a cycle.

Sources read: `literature/stacks-project/derived.tex`, the complete lemmas and
proofs labelled `lemma-derived-functor` (05SA), `lemma-injective-acyclic` (05TH),
and `lemma-enough-injectives-right-derived` (05TI); and the current blueprint's
`thm-pur-rank-one-local-calculation.proof.md`, including its final site-comparison
sentence. The item is explicitly an agent-formulated calculation, not a literal
quotation of these Stacks tags. No source-based statement correction is needed.
The prescribed example CompactObject module is currently withdrawn; its module
header was read, and the active module-mode conventions in the brief are followed.

Edge cases checked: zero objects and zero complexes; identity augmentations into
injective single complexes; the identity sigma and the two identity functors;
nonidentity sigma, retained in the actual termwise comparison; complexes with a
negative integer lower bound; arbitrary maps of augmentations, including zero
maps, without requiring f, g or t to be invertible; independent universes for all
three categories. Neither U nor E nor H is assumed to preserve quasi-isomorphisms.
The hypothesis that UJ is termwise injective is retained explicitly and is not
assumed for all injectives under U. The normalization is required only on the
stated common-injective-complex locus. There are no disputed statements or node
faults.

Searches for reuse:

- `msearch.py leanfinder`: normalized composite comparison on a common augmented
  injective resolution, naturally in augmentation maps. Eight hits, including
  `Functor.rightDerived_map_eq` and `InjectiveResolution.isoRightDerivedObj_*`:
  these give per-degree or individual-functor computations, not this entire
  D⁺-valued normalized composite statement.
- `msearch.py loogle`: `CategoryTheory.Functor.rightDerivedNatTrans_app`, one hit.
  Its full source signature was read; it characterizes a particular derived
  natural transformation rather than this supplied b with two augmentations.
- `msearch.py grep`: `rightDerivedNatTrans_app|isoRightDerivedObj_hom_naturality|rightDerivedFunctorComparison_fac_app`
  in Mathlib CategoryTheory, six hits. The candidate sources were read; none is
  the whole comparison plus its three naturality equations.
- `msearch.py leansearch`: normalized comparison between composite right derived
  functors computed on a common augmented injective resolution by the original
  natural isomorphism. Eight hits, including `rightDerivedNatIso` and
  `isRightDerivedFunctor_iff_of_iso`, no exact match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for normalized comparisons
  and augmented resolutions; then exact item-id search and all six proposed
  declaration names. No match for this item or these declarations. Nearby
  specialized normalized comparisons do not state the abstract calculation.
- `rg` in Mathlib, WeilConjectures and Sheaf for a bounded-below single-complex
  functor found the existing unbounded single functor, single functors in the
  bounded homotopy and derived categories, and application-specific constructions;
  no generic bundled `A ⥤ CochainComplex.Plus A` single functor was found.
  The helper simply lifts the Mathlib single functor and defines no new complex.
- Read `Functor.mapHomotopyCategoryPlusCompIso` in Mathlib and its upstream
  identity-normalization lemmas, as well as the ordinary termwise complex map.
  The existing construction is used directly for every occurrence of sigmaJ.

Server validation: `scompile.py` compiled the final module in both its isolated
sandbox and final library module contexts with no errors or warnings (8.5 s and
7.8 s). The module has `set_option autoImplicit false`; every universe and variable
is explicitly bound. All three theorem proofs are `sorry`; no definition has
postponed data. The node JSON retains one-space indentation, Unicode, and a final
newline. Only `lean` differs from the source node.

## Second reading by Q156

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
