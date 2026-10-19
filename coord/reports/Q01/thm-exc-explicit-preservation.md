## Worker report

The primary module is `Sheaf.Paper.ExplicitExceptionalPreservation`, with theorem
`AlgebraicGeometry.Scheme.explicitExceptional_preservation`. It states the node on the
ordinary unbounded derived category of the recorded constant-ring module sheaves. The
exceptional right adjoint is written using its specified inverse-image identification.
No mathematical statement correction is made.

Hypotheses and clauses, individually:

- A prime ell is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
- `hn : ℕ` indexes the positive exponent `hn + 1`; `Nat.le_add_left 1 hn` is its
  positivity witness. This ranges over exactly all exponents at least one. Coefficients
  are the existing `Padic.coefficientExtensionRing l E (hn + 1)`, retaining the recorded
  valuation ring and chosen uniformizer. The finiteness instance is the existing
  `Padic.finite_coefficientExtensionRing` specialized to that positive exponent.
- `V X : Scheme.{u}` are arbitrary schemes. `hX` and `hV` assert that l is a unit in
  every local ring, precisely invertibility of l on the two schemes. No finite-type,
  Noetherian, separated, or finite-field hypothesis is imposed on the main theorem.
- `_hf : IsOpenImmersion f ∨ (IsFinite f ∧ Etale f)` is exactly the two morphism cases.
- `explicitExceptionalPullback f A` specializes the existing
  `proEtaleRingDerivedPullback` to `proEtaleConstantRing X A` and
  `proEtaleConstantRing V A` using the canonical `proEtaleCoefficientInverseImageMap`.
  Its inverse is the inverse of that actual isomorphism; no free identification is
  assumed. This is Rf^times under the adjunction identifications in the node. The
  accompanying dependency modules state those adjunctions on this exact category.
- The first conjunct quantifies over every `a b : ℤ`, `hab : a ≤ b`, and derived
  object K. It maps membership in the recorded `finiteTorsionConstructibleIn` on X
  to membership in precisely the same inclusive interval on V.
- The second conjunct quantifies over `c d : ℤ` with `c ≤ d` and K. Its hypotheses
  are `intrinsicFiniteTorsionConstructible ... X K` and
  `HasProEtaleTorAmplitude X ... K c d`. Its conclusion is the same Tor interval
  for the inverse image on V. The Tor predicate tests all module sheaves on V,
  not only inverse images of module sheaves on X.
- The third conjunct quantifies over all `hm : ℕ`, `hmn' : hm ≤ hn`, and all derived
  objects K, without boundedness, constructibility or Tor assumptions. It asserts
  `IsIso` for the component of `explicitExceptionalCoefficientComparison`.
  The map is B-linear because its target category is the recorded derived category
  of modules over `Padic.coefficientExtensionRing l E (hm + 1)` on V.
- The actual quotient homomorphism, including its identity case, is
  `flatModelReductionCoefficientMap` at exponents `hm+1 ≤ hn+1`; its sheaf map,
  ordinary scalar extension and universal derived scalar extension are the existing
  `flatModelReductionRingMap`, `flatModelReductionChange` and `flatModelReduction`.
- The comparison is the conjugate of the canonical
  `proEtaleRingRestrictionDerivedDirectImage` comparison. This is the inverse-image
  coefficient comparison: transposition under pullback/direct-image and
  tensor/restriction adjunctions sends it to identity on the underlying sections.
  The latter comparison is fixed by its identity-on-sections and derived-unit
  characterization. Constant-ring naturality supplies the actual commuting ring
  square. The scalar adjunctions are uniquely normalized by `1 tensor x` before
  deriving and by the universal K-flat counit afterwards. Thus the definition
  does not select an arbitrary isomorphism between the two derived objects.
- The final clause quantifies over every quotient and every ordered Tor interval.
  For bounded constructible K with that Tor interval, it asserts bounded
  constructibility and Tor amplitude `[c,d]` over B for BOTH displayed sides:
  reduction of the A-valued inverse image and the B-valued inverse image of the
  reduction. No cohomological preservation under a nonflat quotient is assumed.
- All bounds are the originally quantified integers. Quantification over positive
  exponents and all their quotients is outside those assertions, so the interval
  bounds are independent of both exponents.

The module's helper declarations only expose the canonical comparison required by the
node. `explicitScalarUnitNormalized` records the same sectionwise tensor-unit formula
with arbitrary ring sheaves, avoiding repeated expansion of coefficient witnesses.
`explicitDerivedUnitNormalized` gives the categorical normalization equation on every
complex representative. It is the universal-counit formula on K-flat representatives;
naturality along K-flat resolutions gives the formula for every complex. The helper
keeps category and localization universes independent, without imposing a new size
assumption on the small site.
`explicitReductionModuleAdjunction_existsUnique` is the ordinary tensor-unit
characterization; `explicitReductionAdjunction_existsUnique` is its K-flat-derived
characterization. Both are named theorems with `sorry` and full construction/proof plans,
owned by the same DAG node as its specified coefficient comparison. The main preservation
theorem has `sorry`. Every data definition is a real construction, a specialization of an
existing construction, or a choice from a uniqueness characterization; no data is `sorry`.

Dependency interfaces read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing the actual coefficient quotient.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations` and its canonical-adjunction module,
  publicly retained by the recorded finite-coefficient operations module:
  `proEtaleRingModulePullback`, `proEtaleRingDerivedPullback`,
  `proEtaleRingDerivedAdjunction`, and the module tensor-unit normalization.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientCommRingMap_isIso`, on the actual
  canonical constant coefficient map, specialized with the discrete topology on
  the finite lifted coefficient ring. The temporary topology is internal to the
  isomorphism definition and adds no theorem hypothesis.
- `Sheaf.Paper.ConstructibleIntervals`: `finiteTorsionConstructibleIn`, whose full
  subcategory is `finiteTorsionConstructibleIntervalCategory`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteTorAmplitude` and its recorded Tor dependency:
  `HasProEtaleTorAmplitude` in `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`.
- `Sheaf.Algebra.Homology.DerivedTensor`: the existing derived tensor used by that
  Tor predicate, with the existing K-flat representative convention.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`. Its ordinary tensor
  and universal derived pair are specialized, without altering them, by the existing
  `Sheaf.Paper.FiniteCoefficientReductionFlatModel` interface used throughout.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`:
  `proEtaleConstantInverseImageMap_naturality`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingRestrictScalars_properties`,
  `proEtaleRingRestrictionDerivedDirectImage`, and its unique normalization.
- The collector `def-weil-scheme-morphism-properties` introduces no extra Lean
  declaration. Its named Mathlib morphism properties are used directly.

The item's statement dependencies gain the already existing reduction, constant-ring
exactness, constant-ring naturality, and ring-sheaf-change nodes whose recorded interfaces
are used by the explicit canonical comparison. No new notion or new definition node is
introduced. Stated proof-dependency modules are imported. The generic upstream open
adjunction and compact-support candidate use an incompatible fixed-value presentation
and old pro-etale import paths; the dependency modules below supply their exact intrinsic
interfaces rather than importing both paths and creating duplicate declarations.

Edge cases checked: the empty scheme and empty open; the identity morphism; a finite
etale morphism with empty fibres or varying sheet count; the identity quotient `hm=hn`;
lowest exponent 1; a nonflat quotient such as reduction of exponent 2 to exponent 1;
zero complexes; negative interval endpoints and singleton intervals; unbounded input
for the comparison. All are included. No nonempty assumption, global constant sheet
rank, quotient-flatness assumption, or extra site-universe equality occurs. The pro-etale
site retains object universe u+1 and morphism universe u, with module values in u+1.

Searches actually run:

- LeanFinder: "Exceptional inverse image for open immersions or finite etale morphisms
  preserves constructible cohomological intervals and Tor amplitude and commutes with
  derived coefficient reduction". Eight generic derived-category support results;
  no exceptional/constructible/coefficient-comparison theorem.
- Loogle: `"upperShriek", "IsConstructible"`. No hits.
- Mathlib grep via msearch: `upperShriek|exceptional.*adjoint|constructible.*torAmplitude`.
  No hits.
- LeanSearch: exceptional inverse image with fixed cohomological/Tor intervals and
  finite coefficient quotients. Service returned Internal Server Error; recorded as
  unavailable, not as evidence of no match.
- Direct ripgrep of upstream WeilConjectures and `lean/Sheaf` by the node id,
  explicit-preservation names, exceptional-adjunction names, coefficient comparison,
  and all proposed declaration names. No exact existing preservation theorem. Existing
  inverse-image, exactness, restriction/direct-image, interval, reduction, and Tor
  interfaces were opened and reused. In particular the recorded Tor notion is not
  replaced by an arbitrary tensor operation or an etale-origin predicate.
- Current server source was checked with `scompile.py --source` for the possible
  finite-etale adjunction module and intrinsic open adjunction module; neither was
  published. Delivery branches were checked read-only: N6's open-adjoint branch is
  present and attaches the generic upstream adjunction; no finite-etale-adjoint
  delivery branch is present. The older N5 sandbox has an unlanded finite-etale
  formulation requiring unrelated unfinished integral interfaces, so those are not
  prerequisites for this exact finite-level formulation.

No STATEMENT-DISPUTED flag or mathematical source error was found.

## Dependency modules

Final second-reader inventory: `def-weil-pbc-proetale-site` and
`def-weil-derived-tensor` are record-only attachments to existing intrinsic
interfaces. The final delivery contains no new dependency module. The paragraphs
below describe the first worker's superseded candidates; see the independent
second reading for their removal and reuse of the now-landed adjunctions.

`prop-exc-finite-etale-adjoint`: the base has no usable Lean record. The new module
`Sheaf.AlgebraicGeometry.FiniteEtaleExplicitAdjunction` states exactness of the actual
sectionwise module direct image, termwise computation of its total derived functor,
and its reverse adjunction to the exact tensor inverse image on arbitrary unbounded
complexes. The second theorem retains the extra finite-type finite-field setting for
compact support. The proper identity-compactification candidate is written literally
as its defining composite of identity extension by zero and derived direct image; it is
naturally isomorphic to direct image and has the same right adjoint. Independence is
asserted only through the already established meaning of the usual notation. The helper
inverse-image specialization and canonical coefficient isomorphism are shared with the
main and open modules. Both theorem proofs are `sorry`, with all six source proof steps
in their docstrings. No statement field of this dependency changes.

`prop-exc-open-adjoint`: the generic recorded declaration is on fixed-value sheaves,
and its import closure conflicts with the finite-coefficient paths used by the intrinsic
constant-ring modules. `Sheaf.AlgebraicGeometry.OpenExplicitAdjunction` states exactly
extension by zero left adjoint to the same canonical tensor inverse image on the full
ordinary unbounded intrinsic derived categories. Its only assumptions are an open
immersion and a finite commutative coefficient ring, including the zero-ring and empty
open cases. Its proof is `sorry` with the exactness/localization proof plan. Only its
Lean record changes, with the required explanation in `lean.note`.

Original-source check: the server literature copies of
`sec-six-functors/sk-prop-sf-rf-shriek-preservation/thm-exc-explicit-preservation.md`
and `prop-exc-finite-etale-adjoint.md` were read in full. The main proof explicitly
identifies the exceptional right adjoint with exact inverse image, pulls back the finite
stratification, pulls back the flat model without changing degrees, and computes the
coefficient comparison on that resolution. The finite-etale proof is the finite-tuple,
permutation-gluing argument followed by exact termwise descent and the proper identity
compactification. The delivery follows those constructions and the reviewed DAG's
explicit arbitrary-scheme/compact-support scope distinction.

Additional dependency-record repairs under §1(B):

- `def-weil-finite-tor-amplitude`: the current record chooses a fixed-scalar sheaf
  presentation. The intervals and reduction functors used here are on the intrinsic
  constant-ring module category. The existing `Sheaf.Paper.FiniteTorAmplitude`,
  `WeilConjectures.finiteTorConstructible` and its integral and field aliases give
  exactly the definition on that category, and are recorded with `existing: true`.
- `def-weil-derived-tensor`: for the same presentation reason, reuse the existing
  `Sheaf.Algebra.Homology.DerivedTensor`, `AlgebraicGeometry.Scheme.derivedTensor`
  and `derivedTensorRing`. This is precisely the K-flat representative total tensor
  used by `HasProEtaleTorAmplitude`, including scalar restriction for a ring map.
  Neither repair adds a module or a duplicate definition.

The current server source and delivery-branch list were checked again: neither the
main preservation module nor the finite-etale explicit adjunction module is published,
and no branch delivering the latter exists. The open adjunction has since been
attached to the generic upstream presentation; its intrinsic dependency module remains
necessary here to state the adjunction on exactly the categories used by this item.
The source theorem and finite-etale proof were reread from the server literature.
The three required search kinds were rerun: LeanFinder returned eight generic derived
support/fraction lemmas, Loogle returned zero hits, and Mathlib grep returned zero hits.
Direct upstream and side-source searches found none of the proposed helper names.


## Validation

The prescribed `scompile.py Q01 thm-exc-explicit-preservation` invocation compiled all
three delivered modules together in dependency order and exited 0, with no errors
or warnings, on 2026-10-16. The main file and both dependency files were checked
individually by the wrapper, including their library-form checks.

The delivery is submitted only to the required `deliver2.py --no-push` dry run; the
second reader performs review and delivery.


## Second reading by Q01

I independently read the node and its five proof steps with the Lean open, then
read the original blueprint theorem, finite-etale proposition, open proposition,
and the parent preservation section on the source server. The section's ambient
finite-type finite-field assumptions concern general exceptional functors. This
node and its reviewed dependency distinguish ordinary open/finite-etale inverse
image on arbitrary schemes from that compact-support setting. The statement below
retains the arbitrary-scheme scope already explicitly present in the node. No
mathematical statement correction or target change is made; no citer audit under
§1(C) is needed.

The earlier Worker report remains as the author's historical report. This section
supersedes its three-module inventory and dependency-record descriptions. The final
delivery has ONE Lean module and two existing-declaration record repairs, with no
new definition nodes and no new adjunction dependency modules.

Objects, hypotheses, and conclusions checked individually:

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. Verdict: exact, including ell = 2.
2. Finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`. I opened CoefficientExtension and
   CoefficientExtensionFinite: the ring is the actual quotient of the spectral
   valuation ring by the power of the chosen uniformizer. Verdict: exact; neither
   E nor the valuation ring is replaced by a residue field.
3. Positive exponent n: `(hn : ℕ)` denotes exponent `hn + 1`, with
   `Nat.le_add_left 1 hn`. The landed finite-etale module supplies its finiteness
   instance from `Padic.finite_coefficientExtensionRing`. Verdict: exactly all
   positive exponents; no extra hypothesis on a coefficient quotient.
4. Schemes and morphism: section variables `{V X : Scheme.{u}} (f : V ⟶ X)` and
   `_hf : IsOpenImmersion f ∨ (IsFinite f ∧ Etale f)`. Verdict: precisely the
   two cases. There is no quasi-compactness assumption on the open immersion,
   no constant sheet count, and no finite-type or Noetherian assumption on X/V.
5. Ell invertible on both schemes: `_hX : ∀ x : X, IsUnit
   (l : X.presheaf.stalk x)` and the identical `_hV` condition. Verdict: exact
   local-ring invertibility. These hypotheses remain even though the more general
   existing inverse-image operation needs no such restriction.
6. Ambient categories: `proEtaleDerivedCategory X A` and its V analogue. I opened
   their bodies: they are the ordinary localization of all cochain complexes in
   SheafOfModules over the sheafified constant ULift ring on the actual small
   pro-etale site. Verdict: exact; no constructible-only, completed, etale-origin,
   or bounded-below category. The site record is repaired as described below.
7. Exceptional right adjoint: `explicitExceptionalPullback f A` is only a
   specialization of recorded `proEtaleRingDerivedPullback` along the actual
   `proEtaleCoefficientInverseImageMap`. Its isomorphism uses
   `finiteCoefficientCommRingMap_isIso`; its inverse is the inverse of this
   actual map. Verdict: the inverse-image identification explicitly permitted
   by the node. I opened the newly landed `exceptionalOpenAdjunction` and
   `finiteEtale_proEtale_exact_derived_adjunction`, together with their
   realization equivalences and transported inverse-image definitions. They
   express this same inverse image by canonical constant-scalar realization.
   The proof must identify these realizations, not assume a new adjoint.
8. Constructible interval: the first conjunct quantifies `(a b : ℤ)` with
   `_hab : a ≤ b`, every K, and sends
   `WeilConjectures.constructibleInterval ... X a b K` to the same predicate
   on V for its inverse image. I opened ConstructibleIntervalsUnordered and
   ProEtaleCohomologicalSupport: this is intrinsic bounded constructibility
   intersected with support contained in `Set.Icc a b`. Verdict: exactly the
   inclusive interval, unchanged, using the CURRENT recorded declaration.
9. Tor interval: the second conjunct quantifies all ordered c,d and K, assumes
   `intrinsicFiniteTorsionConstructible ... X K` and
   `HasProEtaleTorAmplitude X A K c d`, and concludes the same predicate on V
   with c,d unchanged. I opened IntrinsicFiniteTorsionConstructibility,
   FiniteTorAmplitude, ProEtaleTorAmplitude, DerivedTensor and its K-flat
   interface. The first predicate is bounded constructible cohomology, and the
   second tests every degree-zero module sheaf on V, via all K-flat resolutions.
   Verdict: no restriction to test sheaves pulled back from X, and no hidden
   flatness hypothesis on K or on the quotient.
10. Every coefficient quotient: `(hm : ℕ) (hmn' : hm ≤ hn)` means exactly
    `1 ≤ hm+1 ≤ hn+1`. `flatModelReductionCoefficientMap` is the actual quotient
    factor map, ULifted; its constant sheaf map is flatModelReductionRingMap.
    The ordinary and derived functors are the existing flatModelReductionChange
    and flatModelReduction, specified on tensors and by the universal derived
    counit. Verdict: exact quotient, including identity, not an arbitrary map.
11. Canonical comparison on EVERY K: the third conjunct has only that quotient
    data and `K : proEtaleDerivedCategory X A`, then `IsIso` of the component
    of `explicitExceptionalCoefficientComparison`. Its target category is
    D(V_proet,B), so the map is B-linear. I traced the definition through
    conjugateEquiv: its source is pullback_A followed by reduction_V, its target
    is reduction_X followed by pullback_B, and its right mate is the existing
    restriction/direct-image isomorphism. That isomorphism is uniquely fixed by
    identity on ordinary sections and the right-derived units. The scalar
    adjunction unit is fixed sectionwise by x -> 1 tensor x followed by
    sheafification; the derived equation fixes it using the universal counit.
    Coefficient naturality gives the actual commuting ring square. Verdict:
    the canonical inverse-image coefficient comparison, with no boundedness,
    constructibility, Tor, or quotient-flatness assumptions on this conjunct.
12. Both sides after reduction: the final conjunct assumes bounded
    constructibility and Tor interval [c,d], then asserts intrinsic bounded
    constructibility AND HasProEtaleTorAmplitude c d over B for each side of
    the displayed comparison. Verdict: every clause present, and the original
    c,d are retained. The a,b and c,d quantifiers do not depend on hm or hn,
    exactly expressing uniformity in both exponents.

Edge cases: empty schemes and the empty open remain included (the invertibility
conditions are then vacuous as they should be); zero objects and zero complexes
are included; finite-etale fibres may be empty and their ranks need not be
constant. The identity scheme morphism and the identity quotient hm=hn are
included. hn=0 and hm=0 mean exponent 1, not the excluded exponent 0. A nonflat
quotient from exponent 2 to 1 is included; the comparison uses arbitrary unbounded
K, whereas bounded constructibility of the reduced terms uses finite Tor input.
Negative and singleton integer intervals are allowed. Reversed intervals are
not required by this theorem, whose node assumes ordered intervals. No field
characteristic restriction beyond ell invertibility was added. The site retains
object universe u+1, morphism universe u and module-value universe u+1; the
normalization helper has independent category, Hom, and derived universes.
There is no extra equality of site object and morphism universes.

Independent searches performed in this reading:

- LeanFinder: "Exact inverse image on small proetale module derived categories
  commutes with scalar extension and preserves bounded constructible objects and
  Tor intervals" returned eight generic Ext/condensed/local-cohomology results,
  none stating this theorem.
- Loogle: `"Sheaf", "changeOfRings"` returned zero results.
- msearch grep: `TorAmplitude.*pullback|pullback.*TorAmplitude|exceptional.*coefficient|
  upperShriek.*constructible` returned zero Mathlib matches.
- LeanSearch: "Inverse image preserves constructible cohomology intervals and Tor
  amplitude and commutes with finite coefficient reduction" returned eight results:
  Scheme.Hom.isConstructible_preimage, abstract inverse-image property declarations,
  extension-closed inverse-image classes, and IdealSheafData.support_comap. None
  states the derived finite-coefficient preservation/comparison theorem. The first
  is the constructible-preimage tool already named in the proof, not this item.
- Direct rg on Mathlib, slopmaster2/WeilConjectures, the side project's
  WeilConjectures framework and lean/Sheaf searched exceptional preservation,
  constructibility preservation, Tor preservation, the blueprint id and proposed
  helper names. Broader matches are generic tools or other exceptional morphism
  cases, not this finite-level conjunction. Exact names of the new declarations
  have no source collision. I also opened the now-landed open and finite-etale
  adjunction modules rather than relying on the author's stale availability claim.

Mismatches found and repaired:

- H4/H13: since the author's search, the actual intrinsic open adjunction and
  finite-etale adjunction have landed. The proposed duplicate dependency modules
  are therefore unnecessary. I removed both files and their dependency-node
  copies, retained the landed records, and imported
  IntrinsicDerivedOpenAdjunction and FiniteEtaleProEtaleAdjunction. The latter
  supplies the coefficient finiteness instance too, so the duplicate instance
  was removed. The four canonical tensor-pullback/comparison specializations
  formerly in that dependency module were moved into the owning main module,
  with source/blueprint tags corrected to this node.
- H4: the first conjunct used the older finiteTorsionConstructibleIn interface,
  whereas the dependency now records constructibleInterval. I replaced the
  predicate/import with that existing recorded definition. The local-ring
  invertibility and interval-order hypotheses remain exactly as before;
  underscore binder names prevent unused-variable warnings after the switch.
- Stale repair: def-weil-finite-tor-amplitude already records the exact intrinsic
  finiteTorConstructible declaration after another landing. I removed its
  redundant node copy, leaving that correct record unchanged.
- §1(B), def-weil-pbc-proetale-site: its current record selects fixed-scalar
  module-valued sheaves; the consumers used here are the already defined
  intrinsic constant-ring modules. I supplied a record-only existing:true
  attachment to proEtaleDerivedCategory, with a precise lean.note. No duplicate
  category or transport assumption was introduced.
- §1(B), def-weil-derived-tensor: I verified and retained the author's record-only
  attachment to Scheme.derivedTensor and derivedTensorRing. The current
  fixed-scalar bifunctor does not type directly in the intrinsic Tor category;
  these existing declarations implement the exact K-flat total tensor and
  scalar-restricted B required by the node. No new tensor definition is delivered.

The recorded operations module publicly retains ProEtaleOperations and its
canonical adjunction interface through ProEtaleFiniteCoefficientDirectImage and
ProEtaleConstantDerivedDirectImage; I opened that import chain. Thus the tensor
specializations use existing recorded operations rather than private replacements.
The only remaining postponed theorems in the delivery are the two uniquely
normalized scalar-adjunction existence statements needed to specify this node's
canonical comparison, and explicitExceptional_preservation. Their complete proof
docstrings specify the generator argument, K-flat localization/uniqueness, and all
five DAG proof steps respectively. Each has this node's source/blueprint tag.
All data are constructions from actual maps/functors or uniquely characterized
adjunctions, and every theorem proof is exactly sorry. No hollow data, private
notion, local notation, or proved theorem is introduced.

Final record inventory: thm-exc-explicit-preservation owns the sole Lean module;
def-weil-pbc-proetale-site and def-weil-derived-tensor are existing-declaration
record repairs. No node's mathematical statement was changed. The main
lean.statement is regenerated verbatim from the final signature.

## Dependency modules (final inventory after second reading)

There are no new dependency modules. The two record-only §1(B) repairs are
`def-weil-pbc-proetale-site` (existing intrinsic constant-ring derived category)
and `def-weil-derived-tensor` (existing K-flat tensor on that category), with the
reasons and exact sources recorded above and in each lean.note. The landed
`prop-exc-open-adjoint`, `prop-exc-finite-etale-adjoint`, and
`def-weil-finite-tor-amplitude` records are left in place.

Final import repair: added the stated proof dependency
`Sheaf.Paper.FiniteCoefficientFlatModel` explicitly, for DAG proof step 3.
The remaining proof dependencies are direct imports or public imports through
the named coefficient, interval, tensor, inverse-image and reduction modules.

Second-reader validation: the final one-module delivery, including the explicit
flat-model proof import and the recorded interval predicate, passed
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q01
thm-exc-explicit-preservation <ExplicitExceptionalPreservation.lean>` with exit 0.
Both sandbox-form and library-form checks completed without errors or warnings.
All variables/universes were checked with autoImplicit=false; the main node
record matches the file signature verbatim and every Lean line is at most 100
characters. The retained existing site/tensor declarations are also checked
by the delivery wrapper probes.

Dry-run repair: all compilation/probes passed, but server preflight required the
site repair id in the exact `## Dependency modules` section. Added the final
inventory there and synchronized the two existing-declaration signature records
with the tool-extracted source signatures. No Lean change was necessary.
