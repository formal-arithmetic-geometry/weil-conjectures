## Worker report

The module `Sheaf.AlgebraicGeometry.CurveOpenConstructibleGeneral` states
`AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_higherDirectImage_of_open_curve`.
Its only theorem proof is `sorry`; no definitions or proofs are added. The node is copied
unchanged except for its `lean` record. No statement correction or new dependency is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The ground field is `(k : Type u) [Field k]`. The disjunction
  `Finite k ∨ ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k` says exactly that it
  is finite or an algebraic closure of a finite field. An abstract finite-field embedding
  can be identified with its image subfield, so the second arm loses no algebraic closure.
  This is the same encoding as the recorded sibling `thm-exc-curve-open-dimension-general`.
- The scheme T over this field is `{T : Scheme.{u}} [T.Over (Spec (.of k))]`.
  `[LocallyOfFiniteType (T ↘ Spec (.of k))]` and
  `[QuasiCompact (T ↘ Spec (.of k))]` together mean finite type, using the convention
  node's named Mathlib definitions.
- The dimension bound is `(hdim : topologicalKrullDim T ≤ 1)`. This is the recorded
  topological Krull dimension, with bottom dimension for the empty scheme.
- An arbitrary open immersion is `(j : U ⟶ T) [IsOpenImmersion j]` with
  `{U : Scheme.{u}}`. There is no extra quasi-compactness, density, reducedness,
  separatedness, connectedness, irreducibility or smoothness assumption on U, T, or j.
- The finite coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`, using the
  commutative-ring module-sheaf convention of the recorded constructible-complexes node.
- A prime invertible on T is `(ℓ : ℕ) (hprime : ℓ.Prime)` and
  `(hinv : IsUnit (ℓ : Γ(T, ⊤)))`. This is invertibility on the scheme itself, including
  the empty-scheme case, rather than an extra characteristic restriction on k.
- Annihilation by a power is
  `(hkill : ∃ n : ℕ, 0 < n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0)`.
  In a unital ring this is equivalent to annihilation of every element by that power.
  Requiring a positive exponent loses no case: if exponent zero annihilates the ring,
  the ring is zero and every positive exponent annihilates it as well.
- The etale A-module sheaf is
  `(F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))` and its constructibility is
  `(hF : Scheme.IsConstructibleEtaleModuleSheaf F)`. The coefficient and fibre universe
  is u+1, exactly as in the recorded constructibility dependency, without an extra
  universe equality assumption.
- Every degree is `(q : ℤ)`, including q < 0 and q = 0.
  The conclusion applies `Scheme.IsConstructibleEtaleModuleSheaf` to
  `H^q ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j) (F[0]))`, rendered by
  `DerivedCategory.Plus.homologyFunctor`, `.obj` of `rightDerivedLowerStarPlus`, and
  `DerivedCategory.Plus.singleFunctor _ 0`. This is exactly R^q j_* F, computed in
  the bounded-below category of the same module-valued sheaves.

Dependency interfaces read and used:

- `def-weil-pbc-scheme-conventions` is a convention-only record, with no declaration or
  module. Its finite-type and open-immersion clauses use Mathlib
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact` and
  `AlgebraicGeometry.IsOpenImmersion`. Their owning modules are imported publicly.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, read as `Order.krullDim (IrreducibleCloseds T)`.
- `def-weil-pbc-constructible-complexes`:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`. Its sheaf clause uses
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, whose full definition and
  docstring were read in `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
  It is the finite locally closed constructible stratification with finite constant module
  values, not the upstream predicate with a different finitely generated-stalk interface.
- `def-weil-pbc-direct-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`, is sectionwise composition with etale base change.
  Its recorded derived declaration `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`
  lives in `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, so that
  actual defining module is imported publicly too. It is the right derived functor of
  that same lowerStar. No private or replacement direct-image construction is introduced.

Every recorded, stated proof-dependency module is imported with ordinary `import`, except
for the statement-dependency modules already public. Mathlib's Noetherian module covers
`pqf-lem-locnoeth-lft` and the Noetherian-open mathlib leaf. The seven-step declaration
docstring carries the node's proof, including the boundary calculation, strict-local algebra,
reduction, branch selection, finite Galois cohomology and lisse point strata. Unstated
proof-only nodes are named there and need no new definitions for this statement.

Edge cases checked before writing:

- T empty: the dimension is bottom and invertibility is automatic in its zero section ring;
  the empty-cover axiom makes the conclusion valid. No nonempty hypothesis is imposed.
- U empty, U = T, nondense U, disconnected/reducible/nonreduced T: all remain allowed.
  The proof uses the finite boundary of closure(U), not a finite complement of U in T.
- Dimension zero is included, as are negative degrees, zero degree, and arbitrarily high
  degrees. Negative and high degrees yield the zero sheaf, which is constructible.
- The zero coefficient ring and zero sheaf are allowed. The annihilation hypothesis does
  not inadvertently exclude the zero ring or demand exact exponent ℓ^n.
- Both the finite ground field and its algebraic closure are covered by the field
  disjunction; no separably closed assumption is added to the finite-field arm.

Searches for an existing exact statement (2026-10-16):

- `msearch.py ... leanfinder`: query "For an open immersion of a curve over a finite field
  or its algebraic closure, higher direct images of constructible finite prime power
  torsion etale module sheaves are constructible". Eight hits, concerning constructible
  subsets under scheme maps, affine transition limits and finite fibres; no sheaf theorem.
- `msearch.py ... loogle`: query
  `IsConstructibleEtaleModuleSheaf, higherDirectImage, IsOpenImmersion`. Zero hits;
  the project-specific first identifier is unknown to the Mathlib search service.
- `msearch.py ... grep`: query
  `constructible.*direct|direct.*constructible|IsConstructibleEtaleModuleSheaf`
  in `Mathlib/AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch`: query "higher direct images along an open immersion of a
  one dimensional finite type scheme preserve constructibility". Service unavailable:
  Internal Server Error. The other search services and direct source searches were used.
- Direct `rg` in `WeilConjectures` and `lean/Sheaf` for the node id and for
  `curve.*[Cc]onstruct|[Cc]onstruct.*curve` finds no exact statement. In particular
  `Scheme.isConstructibleSheaf_lowerStar` in upstream
  `EtaleCohomology/Purity/RealSheaves/Boundary.lean` is only degree zero for a lisse sheaf
  on a curve with finite complement and uses the other constructibility interface;
  its complete signature and docstring were checked and do not match this node.
- The upstream-name index and Mathlib/source/project text searches for the proposed full
  theorem name find no collision. The sibling `CurveOpenDimensionGeneral` is a vanishing
  theorem, not this constructibility statement. No exact existing declaration was found.

No STATEMENT-DISPUTED flag or node fault was found. The source blueprint markdown named
by the node is absent from this read-only mirror; no source-based correction was made.
The copied node's complete statement and seven proof paragraphs supplied the statement
and proof plan, with the recorded interfaces checked in their full source declarations.

Validation: `scompile.py N6 thm-exc-curve-open-constructible-general` compiled the delivered
module cleanly in sandbox and library contexts (5.8 s / 6.4 s), with no errors or warnings.
The required delivery dry run is run after this report is saved; its final result is
reported by the worker response. The independent second reading is left to the second reader.

## Second reading by N6

I independently opened the sandbox node and Lean module, all four statement-dependency
nodes, and the defining declarations rather than relying on their names. The Lean says
exactly what the node says; I found no mathematical mismatch requiring a signature change.
There are no new nodes, dependency modules, or statement corrections in this delivery.

Source check and correction to the worker report: the source is absent from this shared
mirror, but it is available in the launcher's local literature archive. I read
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-curve-open-constructible-general.md` there, including both proof paragraphs,
and the containing `_section.md`. The theorem's statement is verbatim the DAG statement.
I also read the source `def-weil-pbc-constructible-complexes.md`: its initial sentence
specifies a finite commutative ring. Thus `[CommRing A]` is the coefficient convention,
not an added restriction relative to the word "finite" in this theorem. The local Stacks
`etale-cohomology.tex`, `definition-constructible` and
`lemma-constructible-quasi-compact-quasi-separated` (095E), gives the module formulation
and the global partition on qcqs schemes; finite rings are Noetherian and finite-type
schemes over fields here are Noetherian. No separatedness assumption from another theorem
was imported. The blueprint theorem explicitly allows any open and both ground-field cases.

My statement checklist, with each object's hypotheses and conclusion matched to Lean:

1. Ground field: `(k : Type u) [Field k]` and
   `hk : Finite k ∨ ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k`.
   Verdict: exact. I read `IsAlgClosure` in Mathlib: it asserts algebraic closedness
   and algebraicity of the extension. A finite field embedded in an algebraic closure
   can be replaced by its image subfield, so the subfield formulation excludes no case.
2. Target scheme over that field: `{T : Scheme.{u}} [T.Over (Spec (.of k))]`.
   Finite type is `[LocallyOfFiniteType (T ↘ Spec (.of k))]` together with
   `[QuasiCompact (T ↘ Spec (.of k))]`. Verdict: exact, as explicitly fixed by
   `def-weil-pbc-scheme-conventions`. The Mathlib finite-type class was read at its
   definition; no implicit proper, affine, smooth, reduced, or separated hypothesis occurs.
3. Dimension: `hdim : topologicalKrullDim T ≤ 1`. Verdict: exact.
   I opened `Mathlib.Topology.KrullDimension`: this is
   `Order.krullDim (IrreducibleCloseds T)`, the chain-length dimension of the dependency,
   valued in `WithBot ℕ∞`, retaining empty schemes and dimension zero.
4. Open source and arrow: `{U : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]`.
   Verdict: exact. There is no density, nonemptiness, connectedness, or extra finite-type
   or quasi-compactness assumption on this arrow. Its induced structure over k is obtained
   by composition when needed in a proof; no extra independent structure is demanded.
5. Coefficient ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
   Verdict: exact by the source coefficient convention and the recorded constructible
   module-sheaf interface, including the zero ring. This uses the established
   `ModuleCat.{u + 1} A` encoding, with no new category of coefficients.
6. Prime and invertibility: `(ℓ : ℕ) (hprime : ℓ.Prime)` and
   `hinv : IsUnit (ℓ : Γ(T, ⊤))`. Verdict: exact. A global unit is the scheme's
   invertibility condition (local inverses glue); no nonempty-scheme assumption or
   independent characteristic restriction has been added.
7. Annihilating prime power:
   `hkill : ∃ n : ℕ, 0 < n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0`.
   Verdict: exact. Killing the unit kills every element by multiplication. A positive
   exponent is harmless: exponent zero can kill only the zero ring, which is also
   killed by exponent one. This does not require the exponent to be exact.
8. Input sheaf: `F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)` and
   `hF : Scheme.IsConstructibleEtaleModuleSheaf F`. Verdict: exact.
   I opened `BoundedConstructibleComplexes.lean` and its public dependency
   `IsConstructibleEtaleModuleSheaf.lean`, including the latter's full definition.
   It requires a finite locally closed partition with constructible parts and etale
   local trivializations by finite constant modules on every part. I also read
   `LocallyClosedStratification`: its domains immerse into the original scheme with
   the specified images. These are the actual dependency's notions, not a substitute
   stalk-finiteness predicate or an assumption that F is lisse on all of U.
9. Degree: `(q : ℤ)`. Verdict: exact for every degree, with no lower or upper bound.
10. Conclusion: `Scheme.IsConstructibleEtaleModuleSheaf` of the object obtained by
    `DerivedCategory.Plus.singleFunctor _ 0`, then
    `rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j`, then
    `DerivedCategory.Plus.homologyFunctor _ q`. Verdict: exactly R^q j_* F on T.
    I read `Etale.lowerStar` in `UpperLowerStar.Defs`: it is sheaf pushforward by
    base change, evaluating F on the fibre product. I read `rightDerivedLowerStarPlus`
    in `Derived.UpperLowerStarCoherence`: it is that functor's
    `rightDerivedFunctorPlus`. The statement concerns this same module sheaf category
    throughout and the correct bounded-below derived direct image, not an arbitrary map.

Edge cases: T empty has dimension bottom and no extra field-characteristic obstruction;
U empty, U=T, nondense opens, and reducible/nonreduced/disconnected schemes are all admitted.
The finite boundary in the proof is closure(U) minus U, not the whole complement. The zero
ring and zero sheaf are allowed. The stratification definition permits zero strata on the
empty scheme; the branch computation permits an empty finite index set. Degrees q<0,
q=0, q=1 and q>1 are all quantified. The prime hypothesis excludes composite/zero primes
as the source requires. All universes are explicitly bound: k and schemes use arbitrary u;
finite coefficients and module values use the recorded u+1 convention. No independent
universe for test objects or additional smallness assumption appears.

Independent searches, with different wording from the worker's queries:

- `msearch.py ... leanfinder`, "A constructible torsion sheaf on an open subscheme of a
  finite type curve has constructible higher pushforwards": eight hits, consisting of
  constructible-subset images/preimages and qcqs section/localization statements, not
  the etale sheaf theorem.
- `msearch.py ... loogle`, `IsOpenImmersion, Sheaf`: no hits; the service reported
  unknown identifier `IsOpenImmersion`, so this alone is not absence evidence.
- `msearch.py ... leansearch`, "Constructibility of all cohomology sheaves of derived
  extension across an open curve with finite torsion coefficients": unavailable,
  Internal Server Error. The unavailable service was not counted as a negative result.
- Direct case-insensitive `rg` over Mathlib, upstream `WeilConjectures`, and project
  `lean/Sheaf` for constructibility with `lowerStar`, `higherDirect`, or `pushforward`,
  plus the full proposed name and node id, found no exact statement/name collision.
  I opened the two closest upstream interfaces. `Scheme.isConstructibleSheaf_lowerStar`
  in `EtaleCohomology/Purity/RealSheaves/Boundary.lean` is degree zero for a finite
  locally constant sheaf on a curve with finite complement and uses the other predicate.
  `boundedConstructible_rightDerivedLowerStar` and its finite-ring specialization in
  `SixFunctors/Etale/Derived/Stability/DirectImage.lean` concern an entire bounded
  constructible complex, the upstream constructibility predicate, and a general morphism
  between finite-type k-schemes with different explicit coefficient hypotheses. Neither
  is the node's declaration on the project's recorded constructibility interface.
  The already landed sibling `CurveOpenDimensionGeneral` is only the q>1 vanishing.
  No module can be dropped in favor of an exact existing declaration.

H5/H6/H8/H9: no definitions or new auxiliary theorems were introduced, and the sole theorem
has exactly `by sorry`. The module and theorem docstrings both name the source and blueprint
id. I matched the theorem's seven proof steps against all seven node paragraphs: degree
reduction; finite boundary; vanishing off it; strict-local/residue/excellence hypotheses;
reduction and selected branches; finite first cohomology; finite lisse point strata.
No proof clause is replaced by a stronger assumption. There are no private/local notions,
file-local notation, unbound variables, or lines exceeding 100 characters. The sandbox
node differs from the shared node only in `lean`; `lean.statement` is byte-for-byte the
signature in the file, through the conclusion before `:= by`.

Changes: retained all correct Lean and node content; appended this independent reading
and corrected the source-availability limitation in the worker report by actually reading
the local source archive. No mathematical statement correction or dependency repair was
needed. The required `scompile.py N6 thm-exc-curve-open-constructible-general` run compiled
this module in both sandbox and library contexts cleanly (5.1 s and 5.8 s), with no errors
or warnings. Delivery dry run and final push follow this recorded reading.
