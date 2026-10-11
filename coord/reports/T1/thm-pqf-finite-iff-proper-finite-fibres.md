## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteIffProperFiniteFibres` states
`AlgebraicGeometry.isFinite_iff_isProper_and_hasFiniteFibres`. Its sole proof is `sorry`;
no definitions or proofs are added. The node is unchanged except for `lean`.

Clause-by-clause correspondence:
- Schemes X and S: `{X S : Scheme.{u}}`, with explicit universe `u`.
- A morphism f : X → S: `(f : X ⟶ S)`.
- S locally Noetherian: `[IsLocallyNoetherian S]`, retaining the source hypothesis.
- Equivalence of (1) and (2): `↔`.
- (1) f finite: `IsFinite f`.
- (2) f proper: `IsProper f`.
- (2) f has finite fibres: `Scheme.Hom.HasFiniteFibres f`; its recorded definition is
  `∀ s : S, (f ⁻¹' {s}).Finite`. The two requirements are joined with `∧`.

Dependencies read in full and used:
- `pqf-def-quasifinite`: `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.HasFiniteFibres`. Read all four recorded definitions and
  docstrings; only the finite-fibres predicate occurs in this statement.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`. Read the class, its affine-cover equivalences,
  and open-immersion preservation declaration. The recorded Mathlib class is equivalent
  to the affine-cover definition, so no dependency repair is needed.
- Mathlib `AlgebraicGeometry.IsFinite` in `Mathlib.AlgebraicGeometry.Morphisms.Finite`
  (imported by Proper) and `AlgebraicGeometry.IsProper` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; read both class signatures and docstrings.

Source checked directly: https://stacks.math.columbia.edu/tag/02OG, Lemma 30.21.1.
Its hypotheses and both equivalent conditions agree with the node. The local
`literature/stacks-project` checkout is absent on this machine, so the primary source
was opened online. The declaration docstring carries both DAG proof steps and every
proof-node citation, following the stage-1 route.

Edge cases checked before writing: empty X gives empty inverse images and is allowed;
empty S admits only empty X and is allowed; fibres outside the image are empty and
finite; identity morphisms have singleton fibres; positive-dimensional proper fibres
are excluded by the finite-fibres conjunct. No nonemptiness, reducedness, connectedness,
affineness, finite-type, characteristic, or properness hypothesis is added. A single
explicit universe covers arbitrary schemes in the project's Scheme encoding. Local
Noetherianity is not automatic for general S; it remains an explicit hypothesis even
though the modern proper/quasi-finite route establishes a stronger general result.

Searches performed:
- `msearch.py leanfinder`, query `finite morphism of schemes if and only if proper with
  finite fibres`: eight hits, including finite implies proper, the proper-and-affine
  criterion, IsFinite, and finite implies locally quasi-finite; no exact statement.
- `msearch.py loogle`, query `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsProper`:
  nine hits, including `IsFinite.iff_isProper_and_locallyQuasiFinite` and
  `exists_isFinite_morphismRestrict_of_finite_preimage_singleton`. Neither is the exact
  equivalence with finite fibres over a locally Noetherian target.
- `msearch.py grep`, query `iff_isProper|finite_preimage_singleton`, subdirectory
  `AlgebraicGeometry`: fourteen hits, including the locally-quasi-finite criterion and
  finite singleton-preimage lemmas, but no exact declaration.
- `msearch.py leansearch`, query `finite scheme morphism iff proper with finite fibres`:
  service unavailable (Internal Server Error).
- `rg` over Mathlib AlgebraicGeometry, project `WeilConjectures`, and `lean/Sheaf` for
  `finite.*(fibres|fibers)|finite_iff|iff_isProper|finite_preimage_singleton`: component
  lemmas and applications only, no exact statement. Read Mathlib
  ZariskisMainTheorem.lean:373–385 to inspect the closest criterion.
- `rg` over `WeilConjectures` for the item id: no declaration tagged with this node.
- `rg` over Mathlib, `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `isFinite_iff_isProper_and_hasFiniteFibres|iff.*[Ff]inite[Ff]ibres|iff.*[Ff]inite[Ff]ibers`:
  no hits; proposed declaration name is fresh.

No new nodes, dependency modules, statement correction, or disputed statement.

Validation: the server single-file compile passed without errors or warnings. The first
dry run identified a malformed blueprint marker in the theorem docstring; it was
corrected to the exact parenthesized marker before rerunning the dry run.

## Second reading by T1

I independently opened the item node, its delivered module, both statement-dependency
nodes and their recorded declaration sources. The node's inventory and Lean rendering
are as follows; every entry passes H3:

- Objects: arbitrary schemes X and S are `{X S : Scheme.{u}}`; `universe u` is explicit.
  The morphism f from X to S is `(f : X ⟶ S)`. Neither scheme is required to be affine,
  separated, nonempty, reduced or defined over a field.
- Sole hypothesis: S is locally Noetherian, rendered by `[IsLocallyNoetherian S]`.
  The recorded dependency `pqf-def-locnoeth` gives Mathlib's class in
  `Mathlib.AlgebraicGeometry.Noetherian`. I read its `component_noetherian` field and
  `isLocallyNoetherian_of_affine_cover` / `isLocallyNoetherian_iff_of_affine_openCover`:
  these identify the every-affine-open form with precisely the node's affine-cover
  definition. No global Noetherian or quasi-compactness hypothesis is introduced.
- Logical conclusion: equivalence of the two conditions is `↔`, with condition (1)
  on the left and condition (2) on the right, for the same universally quantified f.
- Condition (1): f finite is `IsFinite f`. I read the Mathlib class in
  `Morphisms/Finite.lean`: affine inverse images and finite induced ring homomorphisms.
  This is finite as a scheme morphism, not merely a finite underlying point set.
- Condition (2), first clause: f proper is `IsProper f`. I read its class in
  `Morphisms/Proper.lean`: separated, universally closed and locally of finite type.
  Universal closedness supplies quasi-compactness; hence this is the standard proper
  notion, including finite type, with no independent hypothesis added to the theorem.
- Condition (2), second clause: finite fibres is `Scheme.Hom.HasFiniteFibres f`,
  conjoined to properness with `∧`. I read all four definitions in the recorded
  `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` module. The declaration actually used
  is `def HasFiniteFibres ... := ∀ s : S, (f ⁻¹' {s}).Finite`, exactly the final convention
  in `pqf-def-quasifinite`. This is every target point, including points outside the
  image; it neither counts rational points nor imposes a uniform bound.

Source: the local Stacks .tex checkout is absent. I opened the primary upstream .tex
at https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex,
`section-applications-formal-functions`, `lemma-characterize-finite` (lines 5431-5487),
and the rendered https://stacks.math.columbia.edu/tag/02OG. The section imposes no
standing extra hypothesis: the lemma introduces arbitrary X, S and f and explicitly
assumes only that S is locally Noetherian. Both conditions match the node and Lean.
The source's preceding coherent-sheaf results do not impose hypotheses on this lemma.

Edge cases: empty X is allowed, with empty finite inverse images; empty S is allowed
(and a morphism to it necessarily has empty source); a non-surjective morphism has
empty fibres outside its image, which the universal quantifier allows. Identity fibres
are singletons. Nonreduced finite fibres are allowed: the predicate counts underlying
points, as the node requires. No characteristic or field restriction occurs. There is
no numerical parameter or index set, so n = 0 and empty-index issues do not arise.
The arbitrary universe u is bound explicitly and shared by the objects in Scheme's
category, as required by its existing morphism encoding; there are no independently
smaller test-object universes or unbound variables.

Independent H4 searches, with wording different from the first reader's:

- `msearch.py leanfinder "proper scheme morphism finite point inverse images equivalent
  finite"`: eight hits, including finite-implies-proper, finite singleton preimages,
  and `IsFinite.iff_isProper_and_isAffineHom`; no matching conclusion.
- `msearch.py loogle "AlgebraicGeometry.IsProper, Set.Finite"`: two hits, the finite
  neighbourhood of one finite fibre and a finite-image restriction result, neither
  this equivalence. I opened `exists_isFinite_morphismRestrict_of_finite_preimage_singleton`
  in `ZariskisMainTheorem.lean`; its conclusion is an existential open neighbourhood.
- `msearch.py grep "HasFiniteFibres|HasFiniteFibers|finite_preimage|iff_isProper"`:
  twenty-five component hits, with no exact theorem. Direct `rg` of Mathlib's
  AlgebraicGeometry, `WeilConjectures`, repository `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `isFinite_iff`, finite-fibre equivalences and the
  proposed full declaration name found no existing matching declaration. The only
  `HasFiniteFibres` definition is the recorded dependency, which this module imports.
- `msearch.py leansearch "A proper morphism of schemes with finite underlying fibres
  is finite"`: unavailable, Internal Server Error; no mathematical verdict inferred.

I also read `IsFinite.iff_isProper_and_locallyQuasiFinite` and
`locallyQuasiFinite_iff_finite_preimage_singleton` in Mathlib. Combining them proves the
node, but neither declaration alone has its conclusion. The ruling on more general
existing theorems does not apply: the closest equivalence concludes local
quasi-finiteness rather than finite fibres. Retaining this statement is correct.

H5-H9: no definitions are delivered, hence no hollow data or private copy. The sole
proof remains `by sorry`. The module and theorem docstrings have the exact blueprint
marker and Tag 02OG; the theorem docstring reproduces both DAG proof steps and all
seven cited proof nodes. Namespace, topic directory, imports and line lengths are
correct. Each import supplies a used declaration. The node's `lean.statement` is
verbatim the signature before `:=`. There are no new definition nodes, dependency
modules, statement corrections, or disputed statements to review under H12-H13.

No mismatch found; no Lean or node changes were needed. This reading adds only this
report section. The server single-file compilation passed cleanly, with no errors or
warnings. Delivery preflight and compilation are checked again by `deliver2.py`.
