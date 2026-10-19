## Worker report

The node is already stated by the published slopmaster2 declarations, so no new Lean module is needed. The existing declaration `DerivedCategory.torAmplitudeIn_Q_obj_of_flat` in `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` states that a cochain complex `P` whose terms are flat and which has `P.IsStrictlyGE a` and `P.IsStrictlyLE b` has `torAmplitudeIn C a b (Q.obj P)`. Specializing `C` to `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} Λ)` and `P` to the bounded complex \(\mathcal E^\bullet\) renders the hypotheses “supported in degrees `[a,b]`” and “flat Λ_T-module sheaves.” The declaration `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn` in `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel` identifies this predicate with the etale tor-amplitude predicate recorded by `def-kun-tor-amplitude`, namely vanishing of the homology object in every degree `i < a ∨ b < i` after tensoring with every sheaf placed in degree zero. Thus the conclusion is exactly tor amplitude in `[a,b]`.

The scheme binder is `T : Scheme.{u}` and the commutative coefficient ring is `Λ : Type (u+1)` with `[CommRing Λ]`, precisely the dependency’s size convention; ordinary sheaves of Λ-modules use `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} Λ)`. No separation, finiteness, constructibility or Noetherian condition is needed. The Grothendieck abelian, monoidal closed and functorial-flat-resolution instances required by the generic theorem are supplied for this category by the etale flat-model module; they are structures on the category, not extra geometric hypotheses.

The node hypothesis `a ≤ b` is the interval ordering in the source statement; the existing generic theorem itself does not need a separate inequality because its stronger general statement also covers empty intervals; we apply it only to the node’s ordered endpoints. The support conditions do not imply `a ≤ b` (the zero complex is a counterexample), and no such implication is used. The complex is bounded by those strict support hypotheses, and every term is required flat by `∀ n, ObjectProperty.flat (P.X n)`. The universal test sheaf and degree-zero placement are rendered by the definition of `torAmplitudeIn`/`hasTorAmplitudeIn`. The cases `a = b`, the zero complex, and the endpoint vanishing conditions are included by the strict support predicates; no nonemptiness or positivity assumption is introduced. The empty scheme and the zero coefficient ring are allowed; a single flat sheaf concentrated in degree `a = b` gives the expected single-degree amplitude. Flatness is tensor-flatness in this monoidal category, not stalkwise data or finite generation.

The primary declaration is recorded under its defining module
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`. The etale equivalence is a
justification of the predicate match in `lean.note`, rather than a second primary declaration.
The combined declarations were successfully compiled through
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel` in a dry run; the following
preflight correctly required the primary declaration to be recorded under its defining module.
The final dry run checks that defining module and the primary theorem. No delivered Lean
file, new node, or dependency repair is needed.

Dependencies used:

- `def-kun-tor-amplitude`: `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn` in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` (the target’s tor-amplitude predicate).
- `def-kun-derived-tensor`: `AlgebraicGeometry.Etale.derivedTensor` in `WeilConjectures.SixFunctors.Etale.Derived.Tensor` (the derived tensor used by the predicate).
- `DerivedCategory.torAmplitudeIn_Q_obj_of_flat`: `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` (bounded flat complexes have canonical tor amplitude).
- `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn`: `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel` (identifies the generic tor-amplitude predicate with the etale predicate).

Searches for an existing declaration:

- `msearch.py ... leanfinder "bounded complex of flat sheaves has tor amplitude"`: returned the canonical t-structure declarations `DerivedCategory.isGE_Q_obj_iff`, `DerivedCategory.isLE_Q_obj_iff`, and related support lemmas; no separate duplicate was found.
- `msearch.py ... loogle "torAmplitudeIn, torAmplitudeIn_Q_obj_of_flat"`: no hits (`torAmplitudeIn` unknown to Loogle).
- `msearch.py ... grep "torAmplitudeIn_Q_obj_of_flat|hasTorAmplitudeIn_iff_torAmplitudeIn" CategoryTheory/DerivedCategory`: no hits from the helper’s narrowed grep query.
- `rg` in `WeilConjectures/`: found `DerivedCategory.torAmplitudeIn_Q_obj_of_flat` at `CategoryTheory/DerivedCategory/FlatModel.lean` and `hasTorAmplitudeIn_iff_torAmplitudeIn` at `SixFunctors/Etale/Derived/Finiteness/FlatModel.lean`; their full signatures and docstrings were read.
- `rg` in `lean/Sheaf`: found only uses in `DescentFirstProperFlatCechModel.lean` and `FlatModelOpcyclesFlat.lean`, with no competing target declaration.
- `grep -rl "lem-kun-flat-bounded-tor-amplitude" dag/nodes`: found this node and downstream `lem-kun-0f1n`; no existing Lean declaration for this node.

No `STATEMENT-DISPUTED` or node fault.

## Second reading by NK

Source reading: I opened the blueprint markdown on the project server at the exact
source place recorded by the node (order 1714), and Stacks `sites-cohomology.tex`,
`lemma-tor-amplitude`, including the complete assumptions and the (2) implies (1)
proof (lines 12431-12468). Both use an arbitrary ringed site and arbitrary
commutative coefficients, with no Noetherian or finiteness assumptions. Specializing
to the constant coefficient ring on the small etale site gives this node.

Object/hypothesis/conclusion inventory and independent comparison:

- Scheme T: instantiate the generic category C with
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, `T : Scheme.{u}`. PASS.
- Arbitrary commutative coefficient ring Λ: `Λ : Type (u + 1)`, `[CommRing Λ]`,
  exactly the recorded etale module-sheaf universe convention. PASS.
- Integers a,b and a ≤ b: `(a b : ℤ)` of the existing theorem, applied at the
  ordered endpoints in the node. The generic theorem actually permits arbitrary
  endpoints; its specialization at a ≤ b is the requested assertion. PASS.
- Complex E of module sheaves: `P : CochainComplex C ℤ`, with that same C;
  these are cochain complexes of all sheaves, with no constructibility restriction.
  PASS.
- Support in [a,b], hence bounded: `[P.IsStrictlyGE a] [P.IsStrictlyLE b]`.
  I opened `CochainComplex.isStrictlyGE_iff` and `isStrictlyLE_iff` in Mathlib's
  `Algebra/Homology/Embedding/CochainComplex.lean`: they say precisely that
  terms below a and above b are zero objects. This is termwise, not merely
  a cohomology bound. PASS.
- Every term flat: `hP : ∀ n, ObjectProperty.flat (P.X n)`. I opened the
  definition in `FromJoel/CategoryTheory/Abelian/Flat/Basic.lean`, which is
  exactness of tensoring on both sides; the ordinary sheaf-module tensor is used.
  There is no finite-generation, locally-free or stalkwise-flat replacement. PASS.
- Regard E in the derived category: `Q.obj P`, the localization of this same
  complex. PASS.
- Tor amplitude in [a,b]: `torAmplitudeIn C a b (Q.obj P)`. I opened its
  definition and the complete etale comparison
  `hasTorAmplitudeIn_iff_torAmplitudeIn`: it tests every sheaf F in degree zero,
  and requires zero homology in every integer q with q<a or b<q, exactly the
  bounded predicate in `def-kun-tor-amplitude`. The etale `torAmplitudeIn`
  abbreviation expands to the generic predicate. PASS.

I read the full surrounding category assumptions on the generic theorem, not only
its short signature: abelian, Grothendieck, monoidal closed braided with monoidal
preadditivity, a derived category and functorial flat resolutions. The etale
module-sheaf specialization has these structures; they impose no additional
hypothesis on T or Λ. The source etale flat-model theorem itself applies this
same generic theorem with exactly this category. I also opened the dependency's
landed `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: its bounded predicate is the
existing upstream `hasTorAmplitudeIn`, and only its lower-bounded variant is new.
I read `def-kun-derived-tensor` and its recorded `Etale.derivedTensor` signature
and definition; it is the tensor used by that bounded predicate. No private
notion, missing dependency, new definition node, dependency repair or statement
correction is needed. The existing signature in lean.statement is verbatim.

Edge cases: zero complex, empty scheme, zero ring, arbitrary characteristic,
negative or zero degree endpoints, and a=b are all allowed. No nonempty index
set is introduced. In the extra generic case a>b the support hypotheses force
all terms zero; this does not exclude or change any node case. I initially
considered adding an etale wrapper, then discarded it after checking this exact
specialization and comparison: it would duplicate the existing statement.

Independent searches, using different words from the worker:
`msearch.py leanfinder "Tensoring a finite complex of flat objects with any object
preserves its degree support"` found Module.Flat exact-tensor lemmas, not this
etale statement; `msearch.py loogle "CochainComplex.IsStrictlyGE,
CochainComplex.IsStrictlyLE"` found five support and single-complex lemmas;
`msearch.py grep "flat.*amplitude|amplitude.*flat|kFlat_of.*flat"` found no
Mathlib match. `rg` over all of upstream WeilConjectures and project lean/Sheaf
for torAmplitudeIn, flat, bounded and kFlat found the existing generic theorem,
the etale comparison and uses of them, but no competing definition. These
searches are recorded in searches.jsonl.

Mismatch repaired: the worker report suggested that strict lower and upper
support implied a≤b. This is false for the zero complex, but not part of its Lean
statement. I corrected that explanation and clarified lean.note: the existing
theorem is applied at the node's ordered endpoints, while its extra empty-interval
cases are harmless. The Lean declaration and the node's mathematical statement
remain unchanged. No new module is delivered, so source/blueprint docstrings,
no-hollow-definition and sorry-only checks on new declarations are vacuous.

Validation: `scompile.py NK lem-kun-flat-bounded-tor-amplitude
scratchpad/ExistingChecks.lean` checked both full existing declarations through the
etale flat-model module, in the sandbox and library contexts (7.7 s and 3.7 s),
without errors or warnings. Their printed full signatures bind all category,
instance and universe arguments; C is inherited from the defining module's
variable block, not an unbound identifier. The required `deliver2.py --no-push`
then printed OK: preflight and existing-declaration compilation passed. The final
delivery contains only the node's Lean record and this report.
