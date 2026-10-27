## What changed

Prove `WeilConjectures.RationalizedSmoothAdjunction.coefficient_comparisons` in
`Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams`. Localize both supplied
integral comparison isomorphisms using their published object and pure-tensor
map formulas. Tensor induction proves naturality on every rational arrow;
localizing the inverse components proves the required inverse normalization.
Transport the given integral unit and counit equations factor by factor.
The published component specifications for scalar associators and unitors
then transport both cocycles and identity normalization.

Factor the repeated unit, counit, cocycle and identity formulas into four
generic predicates and twelve named specification components. Their
specializations unfold to the original equations,
with the same quantifiers, functors, components and orientations. This avoids
repeated elaboration of large scheme-specific expressions. Existing theorem
signatures, instances, public imports and docstrings are retained. Local
irreducibility attributes prevent conversion from expanding large chosen maps;
the existing P instances are re-registered locally after sealing that abbreviation.
The concrete coefficient section also keeps the derived-category instance,
integer-ring and uniformizer constructions, the constructibility predicate,
integral linear-structure wrappers and ambient preadditive instance folded.
The coherence arguments also keep localization and full-subcategory category,
preadditive and linear instances folded. Explicit heterogeneous object/map/unit/counit
formulas allow the localized functor body to stay folded in the coefficient
helpers and the main comparison proof. These local settings end before the
original condensed-realization proof.
The generic laws and coefficient helpers live outside the large geometric
section context; they no longer repeatedly elaborate unused r/c presentation data.
Private proved equations keep the raw unit/counit and functor-map formulas in the
canonical scheme notation. A generic constructor for the existing
`LocalizedAdjunctionData` supplies the same record as the old `raw_exists` proof,
with its geometric specialization performed only once. A private proved
`LiftData` API records the object and morphism equations of a functor commuting
with localization. Its composition rule and four abstract
diagram-transport theorems prove the unit, counit, cocycle and identity equations
without unfolding coefficient fields or derived categories. The concrete
coefficient helpers instantiate this API. The coherence lemmas use the same
generic predicates as their callers. Comparison witnesses are extracted once,
and the finished record is used abstractly for the cocycles and identity normalization.
Coefficient inclusions carry explicit source and target intermediate fields.
The transport applications also give their source and target categories
explicitly, avoiding reconstruction of this data from morphism types. The final
assembly proof also keeps the coefficient-transition abbreviations
folded, and the instance-search bound is reduced from 4096 to 512. No
transparency option is disabled. Proof elaboration runs sequentially. The
coefficient proof explicitly destructs the retained algebraic-closure assumption;
the original anonymous binder and every linter are retained.

In `Sheaf.Paper.SfRationalizationKaroubi`, add proved object and pure-tensor
map equations for the existing unique scalar-extension functor. No existing
declaration in that module changes. Extend its existing node attachment.
The item has no downstream importers, and the API module is unclaimed;
there are no forced adaptations. See
`coord/changes/S5-rationalized-comparison-laws.md`.

## Proved and sorry left

The item originally contains three holes. A complete proof body replaces
`WeilConjectures.RationalizedSmoothAdjunction.coefficient_comparisons`.
The item type-checked without profiling in 58.2 seconds using sequential proof
elaboration. The supporting API module compiled in the delivery check in
47.0 seconds. The retained closure assumption is now explicitly destructed in
the coefficient proof to remove its unused-section-variable warning. The
required delivery command checks this final source and records its results.

Two original holes remain, with their original source and proof docstrings;
both belong to `lem-pur-rationalized-smooth-adjunction-diagrams`:

- `WeilConjectures.RationalizedSmoothAdjunction.integral_linear`.
- `WeilConjectures.RationalizedSmoothAdjunction.rationalized_smooth_adjunction_diagrams`.

Holes added: zero. Split-off statements: zero. All new helpers and API lemmas
have complete proofs. The four predicates contain their actual equations.
This is a partial proof delivery conditional on the existing declarations,
including the still-open integral-linearity clause.

## No longer needed

No imports removed; no nodes or modules withdrawn. The proof uses the existing
rational scalar extension and its prescribed associator and unitor directly,
without introducing another scalar-extension construction or any new dependency.
Steps 5--7 of the node are realized; the unit route is preserved. The remaining
clauses retain their recorded dependency plans.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The equivalent generic law predicates and
proved scalar-extension API address elaboration costs. The resumed check found
an unqualified attribute before the namespace was opened, a duplicate attribute,
and P instance lookup failures after locally sealing its abbreviation; these
are proof-context repairs. The final performance repair keeps large instance
data and transition abbreviations folded and uses a smaller instance-search
bound. Temporary profiling settings have been removed.
The local mirror lacked `KFlatIndependentCoefficients.olean`; subsequent compiles
use the supported server-only mode. No launcher script or build artifact was
edited.

The integral compact-support functor has no immediately matching scalar-linearity
instance in the supplied completed coefficient action; its original hole stays.
The final theorem also needs existence of the condensed `Endpoints` and normalized
`HomComparisons`, separately from the proved `realization_agreement` cancellation
identity. That original hole is retained.

The component calculations work for zero objects and torsion Hom modules, for
identity coefficient inclusions, and for arbitrary rational isomorphisms: they
use tensor induction and localized inverse equations, with no integral lift of
a rational inverse. All chosen comparison data are pinned by their component
formulas, which determine them uniquely up to the equality used downstream.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
