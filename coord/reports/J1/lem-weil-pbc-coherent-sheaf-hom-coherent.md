## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentSheafHom` states
`AlgebraicGeometry.Scheme.Modules.isCoherent_homObj`, with proof `sorry`.
No definitions, auxiliary nodes, dependency replacements or statement corrections were needed.

Hypothesis and conclusion matching:

- “Let X be a scheme” is `(X : Scheme.{u})`, with explicit arbitrary universe `u`.
- “F, G are O_X-modules” is `(F G : X.Modules)`. This is the Mathlib category of
  module sheaves over the structure sheaf on the site of open subsets of X.
- “F is coherent” is `hF : RingedSpace.IsCoherent X.toRingedSpace F`.
- “G is coherent” is `hG : RingedSpace.IsCoherent X.toRingedSpace G`.
- The specified H = Hom_{O_X}(G,F) is exactly
  `SheafOfModules.homObj (R := X.sheaf) G F`, with argument order G then F.
  Its sections at U are morphisms between restrictions to the localized open site;
  the over-category of U identifies with its smaller opens, hence these are precisely
  the O_U-linear maps of the two restrictions in the node's parenthetical formula.
  The definition includes restriction maps and the structure-sheaf scalar action.
- “H is coherent” is the conclusion `RingedSpace.IsCoherent X.toRingedSpace (...)`.
- The final parenthetical sentence explains the stronger Stacks theorem and why the
  hypotheses imply finite presentation; it adds no assertion to the scheme theorem.
  This explanation is carried by the five-step proof docstring.

Dependency declarations read and used:

- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.Coherent`,
  `AlgebraicGeometry.RingedSpace.IsCoherent`. Its full definition is finite type plus
  finite-type kernels for every map from a finite free module on every open, not the
  source project's weaker quasi-coherent-plus-finite-presentation predicate.
- `def-pur-sheaf-hom`:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`. Its full signature and docstring were read, including the
  underlying presheaf, sheaf condition and sections equivalence.

Edge cases checked before writing: the empty scheme is allowed (all local conditions
are vacuous); F = 0 or G = 0 gives the zero internal Hom, which is coherent; no
nonemptiness, Noetherian, affine, finite-presentation, characteristic or base-field
hypothesis was added. Finite free presentations may have zero generators or relations.
On the opens site the universe maximum in homObj is u, matching the dependency's
SheafOfModules.{u} carrier. No new universe restriction or auto-bound variable occurs.

Source checked: the local literature/stacks-project/modules.tex checkout is absent on
this machine. The source was read directly at https://stacks.math.columbia.edu/tag/01CQ:
Lemma 17.22.6 states the finite-presentation/internal-Hom result for ringed spaces and
its coherent-target consequence. Together with coherent-implies-finite-presentation
(01BW, as unfolded in the node proof), this gives exactly the present specialization.
The declaration docstring carries all five node proof steps and their dependency IDs.

Searches for an existing theorem (2026-10-11):

- `msearch.py ... leanfinder "The internal sheaf Hom of two coherent modules on a scheme
  is coherent"`: eight hits, comprising the module/sheaf categories, their morphisms,
  abelian/category structures and sheaf predicates; no coherence theorem.
- `msearch.py ... loogle "SheafOfModules.homObj, AlgebraicGeometry.RingedSpace.IsCoherent"`:
  zero hits; unknown identifier SheafOfModules.homObj (it is a project declaration).
- `msearch.py ... grep "IsCoherent|isCoherent|homObj" AlgebraicGeometry/Modules`:
  zero Mathlib hits.
- `msearch.py ... leansearch "internal Hom sheaf of coherent sheaves is coherent"`:
  service unavailable, Internal Server Error; no verdict inferred from this failure.
- `rg` of `IsCoherent|sheafHom|internalHom` in project and Sheaf algebraic-geometry /
  category-theory directories located the recorded coherence definition and unrelated
  Hom constructions. `rg` of the item ID and of coherent/Hom phrases throughout
  WeilConjectures and lean/Sheaf found no existing theorem for this node.
- Exact-name search `isCoherent_homObj` in dag/lean_names_upstream.json, all Mathlib,
  WeilConjectures and lean/Sheaf returned no match. The source Modules/Coherent.lean
  has no Hom-coherence result and uses a different coherence predicate.

Validation: scompile.py J1 lem-weil-pbc-coherent-sheaf-hom-coherent compiled the module
on the server in 1.6 seconds, exit code 0, without warnings. The node's lean record
copies the declaration signature verbatim and preserves all other fields.

## Second reading by J1

Independent reading of the node, its dependency declarations, and
`Sheaf/AlgebraicGeometry/CoherentSheafHom.lean`:

- Object `X` in the node (“a scheme”) is the explicit binder
  `(X : Scheme.{u})`; no nonemptiness, separation, Noetherian, finite-type, or
  field hypothesis is introduced.
- Objects `F` and `G` in the node (“coherent O_X-modules”) are exactly
  `(F G : X.Modules)`, and the two hypotheses are respectively
  `hF : RingedSpace.IsCoherent X.toRingedSpace F` and
  `hG : RingedSpace.IsCoherent X.toRingedSpace G`.  The dependency declaration
  `AlgebraicGeometry.RingedSpace.IsCoherent` is the node's finite-type plus
  finite-type-kernels predicate, with the same sheaf-of-modules carrier.
- The node's `H = Hom_{O_X}(G,F)` is rendered exactly by
  `SheafOfModules.homObj (R := X.sheaf) G F`.  The recorded dependency
  `SheafOfModules.homObj` defines sections on each localized open as
  O-linear maps between the restrictions, with the same restrictions and
  scalar action; its argument order is `G` then `F` as required.
- The conclusion “H is coherent” is exactly
  `RingedSpace.IsCoherent X.toRingedSpace (...)`, with no weakened or extra
  clause and with the same quantifier order.

The source page for Stacks Lemma 01CQ states the ringed-space finite-presentation
internal-Hom result and its coherent-target consequence.  The node specializes
this to a scheme with both modules coherent; its five proof steps (local finite
presentation, restriction, local kernel, coherence, and gluing) are all present
in the statement docstring with the cited dependency IDs.  The source therefore
supports the statement as written.

Edge cases checked: an empty scheme is allowed and the local conditions are
vacuous; either module may be zero, giving the zero coherent Hom; finite free
presentations may have zero generators or relations; no characteristic, base
field, affine, or dimension assumption is hidden; and the explicit universe
`u` permits every scheme universe while `homObj` has the matching carrier.

Searches for a duplicate notion or theorem were repeated with `rg` over
`WeilConjectures`, `lean/Sheaf`, the DAG names, and Mathlib, and with
`msearch.py` LeanSearch, Loogle, LeanFinder, and grep queries for coherent
internal Hom.  They found only the recorded `IsCoherent` definition and
`homObj`; no theorem with this statement exists.  The LeanSearch service was
unavailable in the worker's query, so that search is recorded as unavailable,
not as evidence of a match.

No mismatch was found and no source or node change was needed.  The module
compiled cleanly with `scompile.py`; its node `lean.statement` is verbatim the
signature from the module.
