## Worker report

Item: `lem-sfb-proper-scheme-coherent-ext-finite`, group Q67, stage 2, 2026-10-23.

The module `Sheaf.AlgebraicGeometry.ProperSchemeCoherentExtFinite` states
`AlgebraicGeometry.proper_scheme_coherent_ext_finite`, with its whole proof `sorry`.
It also constructs the structure-morphism scalar homomorphism `Scheme.Hom.extScalarSections`
and the resulting module `Scheme.Hom.coherentExtModule`. Both definitions have real data;
neither depends on a postponed theorem. These are helpers for the scalar action explicitly
specified by this item, not a new independent notion or a choice of an arbitrary action.

Read Stacks `literature/stacks-project/perfect.tex`, `lemma-ext-finite` (Tag 0D0D),
including its proof. Its L is the node's E. Its categories are the Zariski module-derived
categories; this is not the étale-site version for algebraic spaces. The accepted stage-1
statement, split and proof are preserved. The item retains its statement and proof unchanged. Only its `lean` record and the two
added, already-landed definition dependencies differ from the live node. No statement
correction or new node is needed; no dependency-node file is delivered.

Hypothesis and conclusion correspondence:

- Commutative Noetherian A: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- Scheme and its named structure morphism to Spec A:
  `(X : Scheme.{u}) (f : X ⟶ Spec (.of A))`.
- Properness: `[IsProper f]`. Mathlib includes separatedness, universal closedness
  and locally finite type; universal closedness supplies quasi-compactness, hence finite type.
- Zariski O_X-module sheaves: `SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
  `moduleRings` forgets the commutative structure of X's actual structure sheaf to rings
  on its space of opens. The imported `ringedSiteModules` is a transparent abbreviation
  for this Mathlib carrier; no different category instance is selected.
- Derived objects: `(K E : schemeDerivedCategory X)`. The abbreviation is exactly
  `DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))`.
  `[HasDerivedCategory.{w} ...]` fixes the localization universe, rather than imposing
  an extra geometric or boundedness hypothesis. No equality between u and w is assumed.
- Every cohomology sheaf of K is coherent: `hK`, quantifying over all `i : ℤ` and applying
  `RingedSpace.IsCoherent` to `(DerivedCategory.homologyFunctor ... i).obj K`.
- Every cohomology sheaf of E is coherent: the same expression in `hE` with E.
- K is bounded above: `hK_bound : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (H^i(K))`,
  with H^i written out using the homology functor. The strict inequality allows any last
  possibly nonzero degree b.
- E is bounded below: `hE_bound : ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero (H^i(E))`.
  There is no upper bound on E or lower bound on K.
- Every integer degree: `(n : ℤ)`, with no nonnegativity restriction.
- Ext^n_X(K,E) is Hom in the derived category: the actual carrier `(K ⟶ E⟦n⟧)`.
  This avoids replacing Ext of complexes by Mathlib's natural-degree Ext of two sheaves.
- Finite generation over A: `@Module.Finite A (K ⟶ E⟦n⟧) _ _
  (f.coherentExtModule K E n)`. This is finite generation as a module, not finiteness
  of the underlying set or finite dimension over a field.
- The scalar action comes from f: `extScalarSections` sends a to the compatible family
  U ↦ `f.appLE ⊤ U ((Scheme.ΓSpecIso (.of A)).inv a)` (with the required inclusion proof).
  Naturality of `f.appLE` supplies compatibility under restriction. The ring laws follow
  from the existing ring homomorphisms. `coherentExtModule` restricts the upstream localized
  sectionwise scalar action along this ring homomorphism using `Module.compHom`.
  This is the same linear structure used by upstream `schemeDerivedScalar`, via
  `SheafOfModules.homLinear` and Mathlib's derived-category `Linear` instance. It is not
  a new scalar action or an extra hypothesis asking for one.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs` (ideals finitely generated).
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and its morphisms,
  `Mathlib.AlgebraicGeometry.Scheme` (locally ringed spaces with affine neighbourhoods).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, the same module;
  `Scheme.ΓSpecIso` from `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` supplies A's
  actual identification with global sections of its spectrum.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`,
  `Sheaf.CategoryTheory.RingedSiteModules`, and its exact Mathlib match `SheafOfModules`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; cohomology is
  `DerivedCategory.homologyFunctor` from its `HomologySequence` sibling.
- `pqf-def-coherent`, clause 3: `AlgebraicGeometry.RingedSpace.IsCoherent`,
  `WeilConjectures.AlgebraicGeometry.Coherent`, is the exact Stacks 01BV definition.
  Its landed Q25 quasi-coherent finite-type record remains untouched; the item's
  `lean.note` explains this coherence choice, as explicitly requested in the return.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs` (top submodule finitely generated).
- `def-pc-derived-category`: shared carrier abbreviation `AlgebraicGeometry.schemeDerivedCategory`,
  `WeilConjectures.AlgebraicGeometry.DerivedCategory`, is imported by
  `WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar`.
- `def-pur-sheaf-modules-hom-module`: `SheafOfModules.homLinear` from
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule` supplies the sectionwise
  linear structure localized by Mathlib. Both owner nodes are now in `stmt_deps`.
- The proof-only imports retain the stated plan: `IsLocallyNoetherian` and the finite-type
  permanence instances from `Mathlib.AlgebraicGeometry.Noetherian`; affine quasi-separatedness
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`; the existing
  `AlgebraicGeometry.derivedSectionsPushforwardComparison` from
  `Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison`;
  `Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType` from
  `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`;
  `AlgebraicGeometry.affineDerivedSections_homology_comparison` from
  `WeilConjectures.AlgebraicGeometry.AffineDerivedSectionsHomologyComparison`; and
  `Scheme.Modules.coherent_affine_sections_finite` from
  `WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite`.
  The new 0D0C and 0D0B proof nodes and the 08DK comparison have no recorded modules yet,
  so there are no guessed imports for them. They are proof dependencies, not missing
  objects needed to type this statement. The theorem docstring carries all six proof steps,
  including the scalar naturality in the two comparisons.

Edge cases checked by reading the definitions and quantifiers: the zero ring and empty
scheme are allowed (no `Nontrivial` or `Nonempty` hypothesis); zero complexes are allowed;
no assertion excludes n=0 or negative n; arbitrary independently chosen upper and lower
bounds are allowed; unboundedness in the other directions is allowed. No projectivity,
flatness, smoothness, perfection or finite Krull dimension is assumed. Universes u and w
are explicitly bound, and `autoImplicit` is false.

Searches (the launcher's exact outputs are retained in `searches.jsonl`):

- LeanFinder: "On a proper scheme over a noetherian ring Ext groups between bounded above
  and bounded below complexes with coherent cohomology are finitely generated modules".
  Eight hits concern HasExt, smallness, injective dimension and the definition of Ext;
  none states proper-scheme finite generation for complexes.
- Loogle: `Module.Finite, DerivedCategory`: zero hits.
- Mathlib grep: `Ext.*(finite|coher)|[Ff]inite.*Ext|ext_finite`, in AlgebraicGeometry:
  nine hits, all extensionality, category extensivity, morphism definitions or finite
  field extensions. No exact theorem.
- LeanSearch: "Ext groups of coherent complexes on a proper scheme over a Noetherian
  ring are finitely generated": eight hits on Ext of objects and its module structure,
  sheaf cohomology, and Ext classes. None is this finite-generation statement.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `proper_scheme_coherent_ext_finite|coherentExtModule|extScalarSections`: no exact declaration.
  The upstream name-index item search also has no match. The broader `sectionsSubring`
  and `schemeDerivedScalar` searches locate the shared localized scalar action reused here.
- Read all statement-dependency node statements and records, the exact recorded Lean
  signatures/docstrings, and the relevant upstream coherence and scalar constructions.
  Coherence already exists upstream; no private replacement or new definition node is added.

Validation: prescribed `scompile.py Q67 lem-sfb-proper-scheme-coherent-ext-finite
<ProperSchemeCoherentExtFinite.lean>` compiled both its sandbox and library-module forms
against the live published server library, without errors or warnings (3.4s and 3.2s).
No global build or direct shared-repository Git command was run.

## Repair of returned delivery cdd041e09a96

H13: removed the sandbox copy of `pqf-def-coherent.json`, so the delivery makes no
change to the landed Q25 coherence record or any of its consumers. Kept
`ProperSchemeCoherentExtFinite.lean` byte-identical, including `RingedSpace.IsCoherent`
in hK and hE. Added the requested item `lean.note`: this is Stacks 01BV finite type
plus finite-type kernels on every open (clause 3 of the dependency's text), rather
than the landed Q25 conjunction of quasi-coherence and finite type. The maintainer's
return explicitly accepts this choice for the item and requests no global rebinding.

Advisory: added the existing, landed owner nodes `def-pc-derived-category` and
`def-pur-sheaf-modules-hom-module` to the item's `stmt_deps`, for the exact imported
`schemeDerivedCategory` carrier and `SheafOfModules.homLinear` action. Neither owner
node is edited. No Lean source, statement, proof, or proof dependency is changed.

The required first dry run of the inherited packet passed as e0450d47e6e, but its
mechanical success does not fix H13. The repair above removes the rejected change.

## Second reading by Q67

A second in-session pass reopened the source lemma, the item, the dependency node and the
full Lean file. It matched each binder and conclusion as listed above. It checked that
coherence is imposed on every cohomology sheaf, the two bounds have the right direction,
the degree is integral, and the conclusion uses the actual Hom carrier with a canonical
A-action rather than an existentially chosen module structure. It also inspected the bodies
of the two helper definitions: only compatibility and ring-law proofs occur in them; no
postponed theorem supplies data. The coherence choice is documented in the item record as requested; the
landed dependency record is retained unchanged, and its sandbox edit is removed. No additional mismatch or statement dispute was found. This pass is the worker's
own check, not a claim of an independent agent review; the dispatcher explicitly prohibits
starting other agents and assigns the independent reading to the maintainer.

The inherited BLOCKED ending concerned reopening an accepted split. Current brief §0
expressly distinguishes that stage-1 gate from this stage-2 assignment, and the current
queue lists this item at stage 2 with no Lean record. This delivery preserves Q122's
accepted split and uses only the prescribed stage-2 compile and delivery wrappers.

Repair self-check: reopened the full Lean file and source 0D0D after reading the return.
The statement still quantifies over all coherent cohomology sheaves, K bounded above,
E bounded below, and every integer n, with the canonical structure-morphism A-action.
Checked that the item signature remains verbatim, all variables and universes are
explicit, and only the named theorem has `sorry`. The scalar helper definitions
remain real constructions. No independent agent was started, per the dispatcher's rule.
