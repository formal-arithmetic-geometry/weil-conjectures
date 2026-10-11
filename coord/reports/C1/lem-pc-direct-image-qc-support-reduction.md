## Worker report

The module `Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction` states the quasi-compact support reduction theorem from Stacks Project Tag 08EV. It uses `Scheme`, `LocallyOfFiniteType`, the derived category, degreewise homology, coherence, and `Scheme.Modules.HasSupportProperOver`. The boundedness hypothesis is rendered as an integer interval outside which every homology object is zero; coherence and proper support are rendered for every integer degree. The conclusion gives a quasi-compact and quasi-separated open immersion `j : X' ⟶ X`, quasi-compact and quasi-separated composite `j ≫ f`, an object `E'` on `X'`, an isomorphism between `E` and its derived open pushforward, and an isomorphism identifying the derived direct image after restriction with the original derived direct image.

Dependencies used: `Mathlib.AlgebraicGeometry.Scheme` (`AlgebraicGeometry.Scheme`); `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (`AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`); `Sheaf.AlgebraicGeometry.DerivedCategory` (`AlgebraicGeometry.schemeDerivedCategory`); `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase` (`AlgebraicGeometry.Scheme.Modules.HasSupportProperOver`); `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage` (`AlgebraicGeometry.schemeDerivedDirectImage`).

Edge cases checked: the bounded interval permits the zero complex and empty support; the statement allows an empty open when all cohomology vanishes. The identity morphism is compatible with the conclusion when `X` is already quasi-compact and quasi-separated.

Searches: LeanFinder “derived direct image restrict to quasi-compact open containing support” (generic derived-category declarations only; no exact theorem); Loogle “Scheme OpenImmersion” (no hit); grep `quasiCompact.*support|restrict.*directImage|derived.*pushforward` in Mathlib/AlgebraicGeometry (no hit); LeanSearch “proper support quasi compact open restriction derived pushforward” (service unavailable, Internal Server Error).

## Earlier second reading (a previous round; superseded)

I reread the node and module line by line. The `f : X ⟶ S`, locally finite type instance, and Noetherian scheme instance `[IsNoetherian S]` appear explicitly; boundedness is the finite integer interval condition; coherence and proper support quantify over every homological degree; and the conclusion includes the open immersion, quasi-compact/quasi-separated conditions, the restricted derived object, and both direct-image isomorphisms. The recorded signature was normalized to the module's `u` and `w` universe names. No mathematical changes were made.


## Second reading by C1

Read the node, every statement-dependency node and its recorded declaration, the
Coherent module, the exact open-restriction infrastructure and Mathlib overEquiv,
and the composition theorem with its derived-unit characterization. The Stacks
source is available locally at /home/ubuntu/c1-stacks-review/perfect.tex, lines
6772–6804 (Tag 08EV). The lemma also assumes finite Tor dimension, but the support
reduction paragraph explicitly uses only assumptions (1) and (2); finite Tor
dimension is used after the reduction. The item's statement correctly isolates
this paragraph. The node itself was not changed.

Object, hypothesis and conclusion checklist (H3):

- Schemes X and S: `{X S : Scheme.{u}}`; matches def-pc-scheme and Mathlib's
  locally affine locally ringed space definition. No field or characteristic.
- Noetherian base S: `[IsNoetherian S]`; Mathlib Noetherian.lean:280 gives locally
  Noetherian plus quasi-compact. No Noetherian hypothesis on X was added.
- Locally finite type f: `(f : X ⟶ S) [LocallyOfFiniteType f]`; the recorded
  class in FiniteType.lean:43 imposes finite-type ring maps on affine pairs.
  It does not require quasi-compactness of f.
- E in D(O_X): `(E : schemeDerivedCategory X)` uses the shared derived category
  of SheafOfModules (moduleRings X.toRingedSpace), not a second category instance
  on X.Modules. The uniform HasDerivedCategory binder supplies localization data
  for X, S and the existential open scheme; removed redundant separate X/S
  localization binders, which could select inconsistent localization structures.
- Bounded cohomology: `hbounded`, an integer interval outside which homology is
  IsZero. Every integer is quantified; no nonnegative-degree restriction.
- Coherent cohomology: `hcoherent`, RingedSpace.IsCoherent in every degree. Its
  definition is finite type plus finite-type kernels of maps from finite free
  modules on opens. This is the dependency's coherent module notion.
- Closed proper support in every degree: `hsupport`, the recorded
  Scheme.Modules.HasSupportProperOver. Opened its definition: its closed subset
  equals the nonzero-stalk locus and its reduced induced subscheme is proper
  over S. This is support itself, not an unspecified larger closed subset.
- Quasi-compact open j:X' -> X: `∃ U : X.Opens`, with X'=U.toScheme and j=U.ι.
  Mathlib's U.ι is the actual open immersion. `IsCompact (U : Set X)` states
  quasi-compactness of the open; `QuasiCompact U.ι` retains the node's morphism
  clause. Removed the unnecessary separate QuasiSeparated j clause.
- Containment of the union of all supports: `∀ (n : ℤ) (x : X),` nonzero stalk
  of H^n(E) implies x∈U. `TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})` is
  applied to the homology module's underlying abelian presheaf; this is exactly
  Scheme.Modules.presheaf, unfolded. This previously missing clause is now explicit.
- Restricted morphism f': `QuasiCompact (U.ι ≫ f) ∧ QuasiSeparated (U.ι ≫ f)`;
  both required clauses remain, with the same source, target and composition.
- Actual j^*E: the derived functor of overFunctor followed by the recorded
  Scheme.Modules.overEquiv U, with its destination explicitly the shared
  SheafOfModules category. E' is no longer an unrelated existential object.
  An existential additivity witness transports the equivalence's functor to the
  shared category instances; it imposes no new hypothesis or geometric restriction.
- Canonical map: the adjunction `adj` is between this exact restriction and
  schemeDerivedDirectImage U.ι; `adj.unit.app E` is E -> Rj_*j^*E. The comparison
  `c` has the orientation Rj_* ⋙ Rf_* ≅ Rf'_* and satisfies the exact derived-unit
  characterization in exists_derivedModuleDirectImageComposition, whose signature
  and docstring were opened. `IsIso (Rf_*.map (adj.unit.app E) ≫ c.hom.app ...)`
  explicitly asserts invertibility of the required composite, replacing mere
  abstract object isomorphisms. Invertibility of a unit does not depend on which
  adjunction between fixed functors is selected: two choices differ by a natural
  automorphism of the right adjoint. Applying Rf_* preserves that automorphism.
  Thus the existential adjunction encoding also asserts the canonical map is an iso.
- In particular Rf'_*j^*E ≅ Rf_*E: the final Nonempty Iso uses this very same
  restricted object. Orientation matches the node. No arbitrary E' survives.

Edge cases: E=0 has empty support and may use U=⊥; the interval condition permits
all-zero homology (even an empty integer interval). Empty X and empty S are allowed;
no Nonempty assumption is used. When f=id and X is Noetherian, U=⊤ is permitted.
There is no n≥0 condition, coefficient field, characteristic restriction or index
family. Arbitrary scheme universe u and localization universe w remain bound;
the localization structures are the same ones required by the recorded D(O_X)
definition and direct-image functors. No independent smaller test-scheme universe
is introduced. The support stalk carrier is explicitly AddCommGrpCat.{u}.

Independent H4 searches, with different keywords from the worker:

- LeanFinder: "bounded coherent complex proper support restriction quasi compact
  neighborhood": eight hits, mostly affine section vanishing on qcqs opens and
  HomologicalComplex supported embeddings; no exact theorem.
- Loogle: "CategoryTheory.Adjunction.unit": found the actual unit projection and
  generic adjunction lemmas, not a support-reduction theorem.
- LeanSearch: "bounded coherent derived complex proper support quasi compact open
  direct image": service unavailable (Internal Server Error), recorded as unavailable.
- rg in Mathlib/AlgebraicGeometry, the source WeilConjectures tree and lean/Sheaf:
  `support.*reduction|support.*[Qq]uasi[Cc]ompact|directImage_qc_support_reduction`:
  ideal-sheaf support lemmas and unrelated étale compact-support files only, no
  existing statement. Further direct searches located the shared restriction,
  overEquiv and ringed-space direct-image/composition declarations used above.

Repairs: support containment was missing; E' was not tied to restriction; the
canonical map was replaced by abstract isomorphisms; duplicate localization
binders could supply distinct structures; the docstring lacked all three proof
steps; the copyright/license header was absent. Repaired these in the item module
only, retaining the correct hypotheses and both properties of f'. Added the
source proof steps with their node IDs. There are no new definition nodes or
dependency modules, no definitions with holes, and only the named item theorem
has sorry. The node's lean.statement is copied verbatim from the repaired signature.
