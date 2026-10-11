## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation` states
`AlgebraicGeometry.Scheme.exists_finiteEtale_lift_of_henselianPair_of_isGRing`.
Its sole theorem has proof `by sorry`; no definitions or proofs were added.
Only the item's `lean` record changes. No new nodes, dependency modules,
statement corrections, or disputed statements are needed.

Source read: https://stacks.math.columbia.edu/tag/0GS2, proof paragraph beginning
“Essential surjectivity when (A, I) is a henselian pair and A is a Noetherian G-ring”.
The repository's cited `literature/stacks-project/pione.tex` is absent on this machine,
so I read the complete corresponding paragraph on the Stacks website. Its completion,
finite-stage descent, approximation and base-change argument agrees with the node.
The theorem docstring supplies all eight node proof steps and their dependency ids.

Hypotheses and clauses:

- A commutative G-ring: `{A : Type u} [CommRing A] (hA : IsGRing A)`.
  `IsGRing` includes `IsNoetherianRing A` in its first conjunct, so no additional
  Noetherian hypothesis is introduced.
- An ideal I: `(I : Ideal A)`.
- The henselian pair (A,I): `[HenselianRing A I]`, as explicitly specified by the
  dependency's mixed Lean record. This is the standard henselian-pair notion;
  the dependency records the equivalence with its finite-algebra idempotent wording.
- A proper morphism f:Y→Spec A: `{Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]`.
- The closed fibre Y₀: `pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))`.
  Its map to Y is `pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))`.
  This is the canonical chosen fibre product, so an extra cartesian-square hypothesis
  is unnecessary.
- Every finite étale Y₀-scheme V: the binder
  `(V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y₀)`
  (with Y₀ expanded in the file). The object's `hom` is its structure map and
  `prop` supplies both finiteness and étaleness. The property ⊤ imposes no extra
  condition on morphisms.
- Existence of a finite étale Y-scheme U: the existential
  `∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y, ...`.
- An isomorphism U×_Y Y₀ ≅ V over Y₀: `Nonempty (Over.mk
  (pullback.snd U.hom (pullback.fst f ...)) ≅ Over.mk V.hom)`.
  Both objects are in ordinary `CategoryTheory.Over Y₀`; therefore the isomorphism
  commutes with their structure maps. The left object is the second projection
  of exactly the required pullback. An isomorphism in ordinary Over is equivalent
  to one in its full finite-étale subcategory, without imposing further structure.

Dependency declarations used (their signatures and docstrings were read):

- `def-weil-pbc-g-ring`: `Sheaf.RingTheory.GRing`, `IsGRing`.
- `def-weil-pbc-henselian-terminology`: `Sheaf.RingTheory.HenselianTerminology`
  documents and imports `Mathlib.RingTheory.Henselian`, `HenselianRing`.
  Strict henselianity and locality are not assumptions of this theorem.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (separated, universally closed, locally finite type;
  universal closedness supplies quasi-compactness, yielding finite type).
- `def-pc-fibre-product`: its Mathlib match is
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullback existence.
- `def-weil-pbc-finite-etale-category`: its Mathlib match is
  `Mathlib.CategoryTheory.MorphismProperty.Comma`, `MorphismProperty.Over`.
  Specialize to `@IsFinite ⊓ @Etale` and ⊤ as the recorded match instructs.
  `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Etale` supply those properties.
  I read `MorphismProperty.Over.pullback` in `.OverAdjunction`: its object is
  the second projection used here. The functor itself is not needed or imported.

Edge cases checked before writing: I=0 makes the closed fibre canonically Y,
so a cover lifts as itself. I=⊤ is compatible with the standard henselian-pair
hypothesis only for the zero ring (I lies in the Jacobson radical); the empty
base then causes no contradiction. The zero ring and empty Y are not excluded:
there is no `Nontrivial`, nonemptiness, field, connectedness, or surjectivity
assumption. The empty finite étale cover is permitted, as are disconnected covers.
No characteristic condition is present. The single explicit arbitrary universe u
allows any input size by choosing a common universe for the ring and schemes,
following Mathlib's scheme morphisms and the upstream henselian lifting theorem.
All variables and universes are explicitly bound.

Searches (2026-10-11):

- `msearch.py ... leansearch "finite etale covers lift from closed fibres over henselian G-rings"`:
  service unavailable, Internal Server Error; no verdict claimed for that service.
- `msearch.py ... leanfinder "finite etale covers of the closed fibre of a proper scheme over
  a henselian G-ring lift to the proper scheme"`: eight hits on étale properties,
  finite global sections and polynomial factorization; no lifting theorem.
- `msearch.py ... loogle "HenselianRing, IsProper, Etale"`: zero hits,
  unknown identifier IsProper in that index.
- `msearch.py ... grep "henselian|IsGRing|finiteEtale" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg -n 'lem-weil-pbc-finite-etale-lifting-approximation|IsGRing|finiteEtale.*henselian|henselian.*finiteEtale'`
  over the upstream WeilConjectures tree, local `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: upstream `HenselianFiniteEtale.lean` contains
  `Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing` and its local-ring
  specialization. I read their full signatures and docstrings. They assert an
  equivalence for arbitrary henselian pairs, without the G-ring assumption;
  they are not exactly this node's G-ring essential-surjectivity assertion.
  The local tree has `IsGRing` and a complete-local-ring lemma, no lifting statement.
- Exact proposed declaration-name `rg` over Mathlib, upstream WeilConjectures,
  local `lean/Sheaf`, and the upstream-name index: no existing declaration.

Verification: `scompile.py K1 lem-weil-pbc-finite-etale-lifting-approximation
<module path>` compiled on the server in 1.8 seconds, exit code 0, no warnings.

## Second reading by K1

I independently opened the repository node, the sandbox node and Lean module, all
five statement-dependency records, the two imported Sheaf dependency modules,
and the Mathlib declarations implementing the other dependencies. No mathematical
or signature mismatch was found; the Lean and node record are unchanged. This
section supplies the independent review, rather than replacing the Worker report.

Source: I read the Stacks source `pione.tex` directly from
https://raw.githubusercontent.com/stacks/stacks-project/master/pione.tex and
checked https://stacks.math.columbia.edu/tag/0GS2. The paragraph beginning
“Essential surjectivity when (A, I) is a henselian pair” assumes a Noetherian
G-ring and inherits the proper scheme over A from the lemma. It concludes
existence of a finite etale lift with isomorphic special fibre. Completion,
finite-stage descent, approximation, and base change in the node agree with
that paragraph. There are no additional ambient field, locality, separation,
or characteristic assumptions to introduce.

Object/hypothesis/conclusion inventory, with a verdict for each:

1. A commutative G-ring A, in particular Noetherian: `{A : Type u}
   [CommRing A] (hA : IsGRing A)`. Verdict: exact.
   `Sheaf.RingTheory.GRing` defines `IsGRing` as `IsNoetherianRing A` conjoined
   with regularity of every prime-localization completion map. I read its
   underlying `RingHom.IsRegular` and `Algebra.IsGeometricallyRegular` definitions;
   these are the recorded dependency notions, not private substitutes.
2. An ideal I of A: `(I : Ideal A)`. Verdict: exact; arbitrary ideal, with no
   maximality or prime hypothesis.
3. The pair (A,I) is henselian: `[HenselianRing A I]`. Verdict: exact under the
   dependency's explicit mixed record. I read `HenselianTerminology.lean` and
   Mathlib `RingTheory/Henselian.lean`: the class requires I in the Jacobson
   radical and monic simple-root lifting. The dependency identifies this with
   its finite-algebra unique-idempotent lifting formulation (Stacks 09XI).
   No henselian-local or strictly-henselian hypothesis has slipped in.
4. A scheme Y and proper f:Y→Spec A: `{Y : Scheme.{u}}
   (f : Y ⟶ Spec (.of A)) [IsProper f]`. Verdict: exact.
   Mathlib's `IsProper` extends separated, universally closed, locally finite
   type; universally closed implies quasi-compact, giving the node's finite
   type condition. This is the recorded `def-weil-proper-morphism` declaration.
5. The closed fibre Y₀=Y×Spec(A)Spec(A/I): the displayed
   `pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))`.
   Verdict: exact. The quotient spectrum morphism has direction Spec(A/I)→Spec A.
   I read `pullback`, `pullback.fst`, `pullback.snd` in `HasPullback.lean` and
   checked the `HasPullbacks Scheme` instance in `AlgebraicGeometry/Pullbacks`.
   The first projection is the map Y₀→Y; there is no unbound Y₀ or missing square.
6. Every finite etale Y₀-scheme V: `(V : (@IsFinite ⊓ @Etale :
   MorphismProperty Scheme.{u}).Over ⊤ Y₀)`, with Y₀ expanded in the file.
   Verdict: exact. I read `MorphismProperty.Over` and `Over.mk` in `Comma.lean`:
   `V.prop` asserts both properties of `V.hom`, while ⊤ imposes no additional
   restriction on morphisms. This is precisely the dependency's Mathlib match.
7. Existence of a finite etale Y-scheme U: `∃ U : (@IsFinite ⊓ @Etale :
   MorphismProperty Scheme.{u}).Over ⊤ Y, ...`. Verdict: exact. U is quantified
   after V, as in the node; neither uniqueness nor a chosen functor is asserted.
8. Isomorphism U×Y Y₀≅V as Y₀-schemes: `Nonempty (Over.mk
   (pullback.snd U.hom (pullback.fst f ...)) ≅ Over.mk V.hom)`.
   Verdict: exact. The second projection of this second pullback has target Y₀.
   Both `Over.mk` objects belong to ordinary `Over Y₀`, so the isomorphism and
   inverse commute with the maps to Y₀. I also read `Over.pullback` in
   `MorphismProperty/OverAdjunction.lean`: its object structure morphism is
   exactly this second projection. An isomorphism in ordinary Over has exactly
   the required meaning; the finite etale subcategory is full for ⊤.

Edge cases: I=0 is permitted and makes Y₀ canonically Y. I=⊤ forces the zero
ring through `HenselianRing.jac`; the empty spectrum is allowed. There is no
Nontrivial, nonempty, connectedness, surjectivity, field, or characteristic
assumption. Empty Y and empty or disconnected covers are admitted. No index
set or numerical n occurs in the signature, so empty indices and n=0 add no
hidden exclusions. The universe u is explicitly declared, all variables are
bound, and all schemes lie in Mathlib's common `Scheme.{u}` category; a larger
common universe accommodates any input sizes. The theorem assumes no extra
instances beyond the structures/property hypotheses listed above.

Independent searches (2026-10-11), using different wording:

- LeanFinder via `msearch.py`: “essential surjectivity finite etale covers
  proper scheme henselian pair”; eight hits on general etale properties,
  standard-etale algebras, and affine spaces, none stating this lifting result.
- LeanSearch via `msearch.py`: “finite etale cover lifting by approximation over
  a henselian G ring”; service unavailable (Internal Server Error), so no
  mathematical absence verdict is based on that service.
- Loogle via `msearch.py`: `HenselianRing, Nonempty`; zero hits.
- `rg -n -i 'etale.*(lift|hensel|approx)|hensel.*etale'` on Mathlib's and
  upstream's AlgebraicGeometry trees and repository `lean/Sheaf/AlgebraicGeometry`.
  I opened upstream `HenselianFiniteEtale.lean`, including its section binders
  and `Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing` signature.
  That statement asserts the entire pullback equivalence for arbitrary
  henselian pairs, without a G-ring assumption; it is not exactly this node's
  G-ring essential-surjectivity statement. The local matches concern different
  etale lifting questions. No exact existing declaration was found.
- Exact declaration-name search over Mathlib, upstream WeilConjectures,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no collision.

H4/H5/H6/H8/H9: no new definition nodes or dependency modules are delivered,
so no extra-node review is needed. Every notion uses its recorded dependency
or Mathlib specialization. There are no definitions with missing data; the
sole theorem proof is `by sorry`, with no additional proof. The module and
statement docstrings identify Stacks 0GS2 and the blueprint id. I matched the
statement docstring's eight numbered proof steps against the node's eight
steps, including their dependency ids. Header, namespace, import paths and
100-character line limit follow the conventions. The node has no statement
correction; no citer-verdict audit is triggered. Its `lean.statement` matches
the file signature verbatim. Changes from the second reading: this report
section only; no mathematical or Lean change was necessary.
