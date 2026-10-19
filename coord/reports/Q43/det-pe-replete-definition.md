## Worker report

The new module `Sheaf.CategoryTheory.RepleteSheafTopos` defines
`CategoryTheory.GrothendieckTopology.IsReplete`. It has real Prop-valued data and
contains no theorem or `sorry`. The item's statement, dependencies, and proof
are unchanged. There are no new nodes or dependency repairs.

Source read: the full current blueprint files
`main-20261015/blueprint/sec-proetale-coefficients/sk-def-pe-replete/`
`det-pe-replete-definition.md` and `_section.md`, and the DAG statement and all
three proof steps. The unit and node agree. No statement dispute or node fault
was found. No repair note exists for this item.

### Hypotheses and clauses

- A site and its topos of sets: `{C : Type u} [Category.{v} C]` and
  `(J : GrothendieckTopology C)`, with `Sheaf J (Type (max u v w))` as the sheaf
  category. This is the existing topology presentation, not another site or
  sheaf definition. For a site presented by `K : Precoverage C` satisfying the
  recorded `K.IsSiteForCoverings`, take `J = K.toGrothendieck`, as the dependency
  module specifies. Repleteness depends on this sheaf category. The predicate
  is also defined for Grothendieck topologies without a chosen family
  presentation, without restricting any site covered by the node.
- An inverse sequence is exactly the quantified functor
  `F : ℕᵒᵖ ⥤ Sheaf J (Type (max u v w))`. Its n-th sheaf is `F.obj (op n)`.
  The transition `F.map (homOfLE (Nat.le_succ n)).op` has source
  `F.obj (op (n + 1))` and target `F.obj (op n)`. Functoriality supplies the
  identity maps and finite composites mentioned in proof step 1.
- The displayed inverse limit and its sheaf property use the dependency's
  existing sectionwise-limit API, not a private tuple presheaf.
  `Sheaf.createsLimitsOfShape` creates limits along `sheafToPresheaf`; evaluation
  preserves limits of presheaves. Thus `limit F` is canonically the sheaf with
  sections `{x : ∀ n, (F.obj (op n)).obj.obj (op V) |
  ∀ n, (F.map (homOfLE (Nat.le_succ n)).op).hom.app (op V) (x (n + 1)) = x n}`.
  Compatibility with the adjacent arrows is equivalent to compatibility with
  all arrows, by finite composition in the natural-number preorder. The
  sectionwise compatible tuple construction already realizes the limit up to
  the unique limit isomorphism; no new notion or theorem is needed here.
- The projection `p_m`, taking the m-th coordinate, is `limit.π F (op m)`.
  The same sectionwise-limit identification identifies its component with
  `x ↦ x m`. The chosen limit object is legitimate: changing a limit cone
  transports each projection along an isomorphism and does not change whether
  it is epic.
- The node defines epimorphism by local lifts after a covering. Both occurrences
  use existing `Epi`: the recorded dependency
  `Sheaf.isLocallySurjective_iff_epi` identifies it with
  `Sheaf.IsLocallySurjective`, which is `Presheaf.IsLocallySurjective J φ.hom`.
  Its image sieve contains exactly those arrows on which the target section has
  a lift; being covering is precisely local surjectivity. This uses no
  sectionwise-surjectivity hypothesis.
- “Whenever all transitions are epimorphisms” is the premise
  `(∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op))`.
- “Every projection is an epimorphism” is the conclusion
  `∀ m : ℕ, Epi (limit.π F (op m))`. This includes m = 0 and every later m.
  The outer universal quantifier ranges over all inverse sequences, not one
  fixed sequence or sequences on a coherent or weakly contractible site.

All category variables and universes are explicitly bound. The universe
`max u v w` includes the site objects and arrows and allows arbitrary larger
section sets through w. No equality of site object and arrow universes or
additional pullback, coherence, contractibility, or limit-existence hypothesis
is imposed. The relevant limits are existing instances.

### Dependency declarations read and used

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, its full docstring and
  definition (the site's isomorphism covers, bind composition, and existence
  of covering pullbacks). Its module specifies the unchanged use of
  `Sheaf K.toGrothendieck`. Imported publicly for this recorded site convention.
- `Mathlib.CategoryTheory.Sites.Limits`:
  `CategoryTheory.Sheaf.createsLimitsOfShape`, the adjacent
  `Sheaf.isSheaf_of_isLimit` docstring and full signature, and the resulting
  `HasLimitsOfShape` instance. They realize the sectionwise-limit dependency.
  Also read `evaluationJointlyReflectsLimits`,
  `evaluation_preservesLimitsOfShape`, and `limitObjIsoLimitCompEvaluation` in
  `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`.
- `Mathlib.CategoryTheory.Sites.LocallySurjective`:
  `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`, its full signature, the
  `Sheaf.IsLocallySurjective` abbreviation and the
  `Presheaf.IsLocallySurjective` and `imageSieve` definitions and docstrings.
  They realize the epimorphism/local-surjectivity dependency.
- `Mathlib.CategoryTheory.Category.Preorder` supplies the natural-number
  preorder category and `homOfLE`; `Limits.limit` and `Limits.limit.π` use
  Mathlib's chosen genuine limit cone. Their definitions and docstrings in
  `Mathlib.CategoryTheory.Limits.HasLimits` were read.

All statement dependencies are publicly imported. The proof dependencies are
exactly the same three nodes, so no further proof-only imports are needed.

### Edge cases and validation

Checked mathematically: a constant identity sequence has isomorphic projections;
for the one-point site this is the usual tower-of-surjective-sets condition;
empty section sets are permitted (there is no section nonemptiness assumption);
an empty covering remains permitted and local surjectivity remains the site
notion; the empty category is permitted; m = 0 is included; no finite-stage or
bounded-index replacement is made. The inverse-sequence index is always ℕ,
so there is no extra nonempty index-set hypothesis to add.

`scompile.py Q43 det-pe-replete-definition` compiled the delivered module cleanly
on 2026-10-16 UTC. A separate scratch probe, compiled through the same wrapper,
confirmed `HasSheafify J (Type (max u v w))` by `#synth`, and checked the full
`Sheaf.isLocallySurjective_iff_epi` type; the use of `Epi` therefore does not
require an extra sheafification hypothesis or universe restriction.
The scratch probe is outside `lean/` and is not part of the delivery.

### Searches for an existing declaration

All remote semantic and Mathlib grep searches used the prescribed `msearch.py`
with group Q43 and item det-pe-replete-definition.

- LeanFinder: “A replete topos: every inverse sequence of epimorphisms of sheaves
  of sets has epimorphic limit projections”: 8 hits. The closest was
  `CategoryTheory.coherentTopology.epi_π_app_zero_of_epi`; the other hits were
  regular-epi sheaf results, `Sheaf.IsLocallySurjective` infrastructure and
  `LightCondensed.epi_π_app_zero_of_epi`. Read the coherent-topology theorem's
  source and full signature. It proves a special-site assertion, with extra
  site and effective-epi assumptions, rather than defining repleteness of an
  arbitrary topos; it is not a match.
- Loogle: `"replete"`: 0 hits.
- Mathlib grep: `Replete|replete|epi_π_app_zero_of_epi`, restricted to
  `CategoryTheory/Sites`: 2 hits, the module introduction and declaration of
  the same coherent-topology theorem. Direct `rg` over Mathlib's
  `CategoryTheory` for `IsReplete|replete` had no hits.
- LeanSearch: “replete topos countable inverse sequence of epimorphisms limit
  projections are epimorphisms”: 8 hits, including the coherent-topology
  theorem, profinite/light-profinite limit projections, a concrete-category
  sectionwise-surjectivity theorem and countable AB4*. None defines this
  general sheaf-topos predicate.
- `rg -n 'Replete|replete'` on upstream `WeilConjectures` and project
  `lean/Sheaf` found only comments mentioning replete topoi, or unrelated
  replete full subcategories. Neither is the present notion. Searching
  `det-pe-replete-definition` in upstream `WeilConjectures` found no match.
  The upstream declaration-name record `dag/lean_names_upstream.json` likewise
  had no repleteness declaration. The proposed full declaration name does not
  occur in the searched source trees.

No second definition of an existing notion is introduced: the new declaration
is only the repleteness predicate, using the existing functor, sheaf, limit,
projection and epimorphism notions.

## Second reading by Q43

I independently read the node, its source place, the dependency records, and
`Sheaf/CategoryTheory/RepleteSheafTopos.lean`.

- The node introduces a site category `C`, its Grothendieck topology `J`, and
  the topos of set-valued sheaves. Lean renders these as
  `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)` and
  `Sheaf J (Type (max u v w))`; this preserves arbitrary object, morphism, and
  section-set universes and adds no finiteness or site hypothesis.
- The node's inverse sequence is Lean's
  `F : ℕᵒᵖ ⥤ Sheaf J (Type (max u v w))`. Its adjacent transition is exactly
  `F.map (homOfLE (Nat.le_succ n)).op`, with the node's source and target.
- The node's limit and coordinate projection are rendered by
  `limit.π F (op m)`. The sectionwise-limit dependency identifies this chosen
  categorical limit with the displayed compatible-tuple sheaf and its
  coordinate maps, so no private limit construction or extra existence
  assumption is introduced.
- The node's local-surjectivity notion of epimorphism is rendered by `Epi`.
  The recorded `Sheaf.isLocallySurjective_iff_epi` dependency gives exactly the
  equivalence for these set-valued sheaves (and the module's imports provide the
  required sheafification instance), so the transition premise
  `∀ n, Epi (...)` and conclusion `∀ m, Epi (...)` have precisely the node's
  meaning.
- The quantifier order is unchanged: all inverse sequences first, then the
  transition hypothesis, then every `m : ℕ`. Thus `m = 0`, all later indices,
  empty section sets, empty/degenerate sites, and constant identity towers are
  included. No nonemptiness, coherence, contractibility, Noetherian, or
  characteristic assumption appears.

The source blueprint and Stacks places (00VH, 00VM, 00W2, 00WM, 00WN) agree
with this formulation. Searches in Mathlib, upstream `WeilConjectures`, and
project `lean/Sheaf` found no existing general repleteness declaration; the
nearby coherent-topology and light-condensed results are special theorems with
extra hypotheses. The three dependencies were opened and their recorded
interfaces are the ones used by the module. There are no new nodes or
dependency repairs, and I found no mismatch to change.
