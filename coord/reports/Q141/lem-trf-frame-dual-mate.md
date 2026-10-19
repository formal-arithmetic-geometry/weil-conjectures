## Worker report

The repair retains the real `frameUnit` and `frameDualMap` constructions and fixes
`CategoryTheory.frame_dual_mate` to state the original DAG statement exactly. The
four maps are chain maps whose evaluation and coevaluation components are now
specified by the canonical formulas. No theorem is proved in this stage: the sole
new theorem, `frame_dual_mate`, has the whole proof `by sorry`. Definitions and
abbreviations contain real data.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative coefficient ring is `{A : Type u} [CommRing A]`; the complexes
  are `P R : CochainComplex (ModuleCat.{u} A) ℤ`. The only universe is explicitly
  declared `u`, and `set_option autoImplicit false` forbids implicit binders.
- Boundedness is `hPbounded` and `hRbounded`, asserting zero objects outside some
  finite integer interval. Finite generation and projectivity in every degree are
  `hPfinite`, `hRfinite`, `hPprojective`, and `hRprojective`.
- The unit `A[0]` is `frameUnit A`, an abbreviation of Mathlib's
  `HomologicalComplex.tensorUnit`. The dual of `B` is the recorded
  `CochainComplex.moduleHomComplex B (frameUnit A)`. Its differential is the
  existing signed total-Hom differential, not a newly specified structure.
- The total tensor, its signed differential, associators and unitors are those
  of the imported canonical cochain-complex monoidal instance. Tensor maps in
  the conclusion are `HomologicalComplex.tensorHom`.
- The explicit finite frames are `nP/eP/εP/frameP` and `nR/eR/εR/frameR`.
  `frameP` and `frameR` are the expansion equations for every element in every
  degree; `hPempty` and `hRempty` impose empty frames on zero terms, as the
  original statement requires. `Fin 0` is permitted.
- `evP/coevP/evR/coevR` have the chain-map types in the node. For each `B=P,R`,
  `hEvB` prescribes `ev(φ ⊗ x) = φ(x)` in total degree zero using
  `HomologicalComplex.ιTensorObj` at `(-i,i)`. The result is in `(frameUnit A).X 0`
  on both sides, so no arbitrary identification with the ring is introduced.
  `hEvBzero` explicitly prescribes zero evaluation outside degree zero.
- For each `B=P,R`, `hCoevB` prescribes the value at the canonical unit element
  `(singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv.hom 1`. It is the sum over
  `i ∈ Finset.Icc a b` and `r : Fin (nB i)` of the `ιTensorObj` image of
  `eB i r ⊗ εB i r`. The functional is embedded in dual degree `-i` by the
  existing `HomComplex.Cochain.single`, composed with the same canonical unit
  coordinate. The formula is stated for every interval supporting `B`; this
  renders the source's finite sum over all degrees without choosing a bound.
  Outside any such interval the frame is empty, so these sums are equal.
  Other components of coevaluation are uniquely zero because its source is
  `A[0]`.
- The two triangle identities for each complex are `hTriP₁`, `hTriP₂`,
  `hTriR₁`, and `hTriR₂`, using the canonical associators and unitors.
- The degree-zero chain map is `f : P ⟶ R`. `frameDualMap f` is the actual
  `CochainComplex.moduleHomPrecomp (frameUnit A) f`, with degree-j component
  `(HomComplex.Cochain.ofHom f).comp φ (zero_add j)`.
- The first conjunct is evaluation naturality for this specified map. The second
  is coevaluation naturality. The last quantifies every chain map `v` with the
  evaluation identity and concludes `v = frameDualMap f`, precisely uniqueness.

Dependency declarations read and used:

- `CochainComplex.moduleHomComplex`, module
  `Sheaf.Algebra.Homology.ModuleHomComplex`: module-valued homogeneous cochains
  with Mathlib's `δ_hom`; this is the recorded total-Hom dependency.
- `Module.Finite`, module `Mathlib.RingTheory.Finiteness.Defs`, and
  `Module.Projective`, module `Mathlib.Algebra.Module.Projective`: the recorded
  finite-generation and projectivity notions.
- The complex category attached to `def-weil-abstract-derived-category` is
  Mathlib's `CochainComplex`; its recorded `DerivedCategory` and
  `HasDerivedCategory` are not additional assumptions in this chain-level lemma.
- `CochainComplex.mapBifunctor` / `HomologicalComplex.mapBifunctor`, module
  `Mathlib.Algebra.Homology.BifunctorShift`, underlie the tensor-complex dependency.
  The specialization to modules is the canonical `HomologicalComplex.tensorObj`
  from `Mathlib.Algebra.Homology.Monoidal`, with the monoidal instance imported
  through `WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex`.
- `CochainComplex.moduleHomPrecomp` and its explicit component definition, module
  `Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy`, supply actual precomposition.
  `HomComplex.Cochain.single`, in Mathlib's
  `Algebra.Homology.HomotopyCategory.HomComplex`, embeds each frame functional.

Edge cases checked: empty frames and zero terms, the zero complex (including an
empty supporting interval), arbitrary supporting intervals, nonfree finite
projective modules (no basis is assumed), characteristic two, and all ring/module
sizes in the explicitly declared universe. Over ℤ with `P=R=A[0]` and `f=id`, the
returned counterexample's sign-reversed evaluation gives -1 rather than 1 on the
unit functional and unit vector; it fails `hEvR`. Thus the new hypotheses exclude
exactly the erroneous arbitrary choice of pairing identified by the reviewer.

Searches retained from the saved packet: `msearch.py` LeanFinder/Loogle/LeanSearch
for finite-frame evaluation/coevaluation naturality and categorical mates, and
Mathlib/project grep for frame duality, finite frames, total Hom, tensor unit,
`HomComplex.Cochain.comp`, and `Cochain.ofHom`: generic rigid-category and module
results, no exact statement. Repair searches: `rg` for
`frame_dual_mate|frameUnit|frameDualMap|lem-trf-frame-dual-mate` in the upstream
`WeilConjectures` and shared `lean/Sheaf` trees found no existing declaration;
`msearch.py leanfinder "Precomposition on the total Hom dual of bounded finite
projective cochain complexes is the unique evaluation mate and preserves finite
frame coevaluation"` returned generic precomposition and rigid mate lemmas, not
this finite-frame statement. `msearch.py loogle
"HomComplex.Cochain.single, HomologicalComplex.ιTensorObj"` returned zero hits
with an unknown-short-name message; the full names and definitions were then
read directly in Mathlib. `rg --files` located `Mathlib.Data.Int.Interval`, which
supplies the finite-interval instance needed by the coevaluation formula.
A further `msearch.py grep
"coevaluation_comp_leftAdjointMate|tensorLeftHomEquiv_whiskerRight_comp_evaluation"
CategoryTheory/Monoidal/Rigid` found the generic rigid duality declarations in
`Rigid/Basic.lean` and one use in `Rigid/FunctorCategory.lean`; they do not state
the explicit total-Hom and finite-frame identification here.
The existing `ChainSupertrace.lean` component formulas were read and followed.
No new independent notion or dependency module is needed.

## Repair of return 233aaaa6a524

- H3: the four previously arbitrary maps now satisfy `hEvP/hEvR`,
  `hEvPzero/hEvRzero`, and `hCoevP/hCoevR`. Both finite frames occur in the
  coevaluation component hypotheses. The triangle identities alone are no
  longer used to identify arbitrary dual structures with precomposition.
- H7b: restored the original DAG statement verbatim, including explicit
  evaluation, coevaluation and empty-frame formulas. The earlier `statement_change`
  is withdrawn: the final delivery changes only the node's `lean` field.
- H8: `frameUnit` now has a source and blueprint docstring. `lean.declarations`
  lists the abbreviation, the real precomposition definition, and the theorem.

## Statement corrected

The saved packet's invalid correction has been withdrawn. Compared with the
current shared base, `statement`, `stmt_deps`, `proof`, and `proof_deps` are
unchanged, and no `statement_change` is needed. The sole citer found by checking
all `stmt_deps` and `proof_deps` is `lem-trf-chain-supertrace`; its use holds.
Its `hEv` and finite-frame coevaluation component equations are precisely the
ones now required here, with its frame-package vectors and functionals. Its
empty-frame condition and boundedness make the displayed sums independent of
the chosen supporting interval. The dual mate's naturality and uniqueness
clauses are retained, so its proof step 12 has the required interface.
The citer is not edited, and no downstream import is added to this module.

## Second reading by Q141

Author self-check, not an independent review: checked the full original node,
its four proof steps, the blueprint proof, the recorded dependency signatures,
and `ChainSupertrace.lean`. Every hypothesis and conclusion is mapped above.
The return's counterexample fails the new component hypothesis. All declarations
have source/blueprint docstrings, all variables and universes are explicit, line
width is at most 100, and the only postponed proof is the named theorem matching
the delivered node. The initial saved-packet dry run passed mechanically, but
its semantic defects were still repaired before delivery. Final validation is
through `scompile.py` and the prescribed `deliver2.py --no-push` preflight.

Validation: the final `scompile.py` run compiled the sandbox and library module
cleanly (36.3 s and 21.1 s respectively), with no errors or unexpected warnings.
The node signature is verbatim, every Lean line is at most 100 characters, and
there is exactly one `sorry`, the theorem proof.
