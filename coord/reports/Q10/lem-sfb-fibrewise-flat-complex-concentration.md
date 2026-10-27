## Worker report

The module `Sheaf.Algebra.Homology.FibrewiseFlatComplexConcentration` states
`CochainComplex.fibrewiseFlat_complex_concentration`, with one whole-proof `sorry`.
It also constructs `ModuleCat.extendScalarsCompOfUniverses` from the actual
extension/restriction adjunctions and their restriction-composition comparison.
This helper is the same mate construction as Mathlib's `extendScalarsComp`, with
independent ring universes. It has real data and contains no postponed theorem.
No new node, dependency replacement, or statement correction is needed.

Source read: `literature/stacks-project/dualizing.tex`, lines 5474–5580,
Tag 0E2F, especially the final two paragraphs, and `algebra.tex`, Tag 00ME,
`lemma-mod-injective`. The former explicitly constructs E, Q^n and Z^0 and
identifies arbitrary base-change cohomology. This node extracts the general
complex argument and specifies its canonical truncation zigzag. Its seven
proof steps are written in the theorem docstring, including flatness of B^1,
cycles after tensoring, the H^0 quotient and naturality. The unit is the remote
stability unit; this input is not its unit statement. No fault was found.

Hypotheses and objects, clause by clause:

- The homomorphism of commutative Noetherian rings R → S is `(R : Type u)` and
  `(S : Type v)`, `[CommRing R] [CommRing S] [Algebra R S]`, and
  `[IsNoetherianRing R] [IsNoetherianRing S]`. Algebra is precisely the supplied
  ring homomorphism, including the zero ring cases.
- E is `CochainComplex (ModuleCat.{max u v w x} S) ℤ`. This is the recorded
  `CochainComplex`, whose morphisms are actual chain maps.
- Vanishing in sufficiently negative degrees is `hbelow : ∃ N : ℤ, ∀ n : ℤ,
  n < N → IsZero (E.X n)`. No upper bound is imposed.
- Finiteness of every term is `hfinite : ∀ n, Module.Finite S (E.X n)`.
- R-flatness of every term is `hflat`, using Mathlib's `Module.Flat` on the
  underlying R-module obtained by `ModuleCat.restrictScalars (algebraMap R S)`.
  Thus the action is the supplied action, not an extra independently chosen one.
- Residue-field concentration is `hfibres`, for every `p : PrimeSpectrum R`
  and every integer `i ≠ 0`. The residue field is `p.asIdeal.ResidueField`,
  appearing through `p.asIdeal.Fiber S = κ(p) ⊗[R] S`; its defining source
  gives the fraction-field-of-R/p interpretation. Extension along
  `Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S` gives
  `(κ(p) ⊗_R S) ⊗_S E`, canonically `κ(p) ⊗_R E`, with its complete fibre-ring
  action. `IsZero (...homology i)` is exactly H^i = 0.
- R-flatness of H^0 is `hzero`, using the same restriction functor on
  `E.homology 0`. No claim that H^0 is automatically flat replaces this assumption.

Conclusions and normalization, clause by clause:

- The middle complex T is the actual `E.truncLE 0`. Mathlib's
  `truncLEXIso` identifies its negative terms with E's, `truncLEXIsoCycles`
  identifies its zero term with `E.cycles 0 = ker d^0`, and positive terms
  are zero. `E.ιTruncLE 0` is the actual inclusion into E.
- The existential `b` is a natural transformation from the good-truncation
  functor to `homologyFunctor ... 0 ⋙ singleFunctor ... 0`. Its displayed
  degree-zero equation is `truncLEXIsoCycles.hom ≫ homologyπ ≫ singleObjXSelf.inv`.
  Thus it is the specified quotient Z^0 → H^0, not an arbitrary map or a
  choice of quasi-isomorphism. Maps to a single complex are determined by
  this component; all their other target terms are zero.
- For every `[Algebra R R']`, the two `QuasiIso` conjuncts are exactly the
  scalar-extended inclusion and the scalar-extended `b.app E`. Scalar extension
  is termwise, via `extendScalars.mapHomologicalComplex`, into modules over
  `S ⊗[R] R'`. The natural canonical identification
  `(S ⊗_R R') ⊗_S M ≅ M ⊗_R R'` sends `(s tensor r') tensor m` to
  `(s • m) tensor r'`; its inverse sends `m tensor r'` to `(1 tensor r') tensor m`.
  Hence the two arrows are exactly the node's S'-linear zigzag arrows.
- The right endpoint is the extension of `(singleFunctor _ 0).obj (E.homology 0)`.
  Extension sends this to the single complex of extended H^0; the canonical
  `singleMapHomologicalComplex` identification accounts for the harmless
  order of single and extension in the notation. No cohomology-only substitute
  for the derived assertion is used.
- `∃ e : Q(E') ≅ Q(H[0]')` together with
  `Q.map(left) ≫ e.hom = Q.map(right)` fixes the derived isomorphism to
  `Q(left)⁻¹ ≫ Q(right)`. Invertibility of Q(left) makes this unique.
- Naturality in chain maps is encoded by the type of `b`, Mathlib's natural
  good-truncation inclusion, and the normalization equation for e. The
  resulting commuting squares force naturality of the unique e for maps
  between any two complexes satisfying the assumptions. This does not add
  a chain map or arbitrary naturality hypothesis.
- The final conjunct records the two actual chain-level associativity squares
  for extension along f followed by g, using the canonical mate comparison
  `extendScalarsCompOfUniverses`. It includes the extension maps in the node,
  and is valid for arbitrary f and g since it is naturality of that comparison.
  Together with the unique normalized e, these squares assert compatibility
  of the specified isomorphism with further scalar extension. The mate is the
  same tensor association as Mathlib's `extendScalarsComp`; three associations
  give the identical product of scalar factors, and identity extension uses
  Mathlib's canonical `extendScalarsId`. No discretionary comparison is chosen.
- R' has an arbitrary commutative ring structure and R-algebra structure only;
  it is neither required flat nor Noetherian. The `HasDerivedCategory` instance
  is the recorded size convention for the localization, not a mathematical
  condition on R'. The module universe includes both ring universes and an
  arbitrary extra module universe; extension rings have an independent x.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, inversion of quasi-isomorphisms.
- `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`, homology-map isomorphisms.
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`: `truncLE`, `ιTruncLE`,
  `truncLEXIso`, `truncLEXIsoCycles`; the embedding truncation functor is from
  `Mathlib.Algebra.Homology.Embedding.TruncLE`.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: `extendScalars`,
  `restrictScalars`, `extendRestrictScalarsAdj`, `restrictScalarsComp`, and the
  signature and body of `extendScalarsComp`. `ModuleCat.Abelian` supplies the
  abelian/module homology instances publicly in module mode.
- `WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel`:
  `ModuleCat.baseDerivedTensor_extendScalars_additive`, reused directly as its
  already published general instance. Mathlib's more specialized adjunction
  instance leaves universe metavariables when extending between independent
  ring universes; importing this exact existing instance resolves them without
  another definition or assumption.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` and `.Fiber`:
  `Ideal.ResidueField`, `Ideal.Fiber`; the latter is publicly imported.
- Proof dependencies are imported without `public`: `rTensor_exact` and
  `lTensor_exact` in `TensorProduct.RightExactness`; `Module.Flat` exactness
  in `Flat.Basic`; `LocalizedModule.map_exact`; `IsLocalizedModule.rTensor`
  and `map_lTensor`; `Module.flat_iff_of_isLocalization`; upstream
  `flat_mod_injective`; `LinearMap.lTensor_injective_of_exact_of_flat`;
  `LinearMap.universally_injective_iff_localizedAtContractedPrime`;
  `Module.flat_submodule_of_universally_exact`; and upstream
  `Module.Flat.of_exact_of_flat_of_flat_right`. The noetherian, localization,
  tensor and derived-category proof-dependency definitions use the same
  publicly imported Mathlib declarations. No already stated proof dependency
  is waiting for another delivery.

Edge cases checked before and after writing: zero complex; H^0 = 0; complexes
with nonzero negative terms (the truncation retains them); unbounded positive
terms; empty prime spectrum for the zero ring (then any unital S is zero);
zero algebra S; zero extension ring; identity scalar extension; nonflat quotient
extension; non-Noetherian extension; maps of complexes without quasi-isomorphism
assumptions; and successive/triple extensions. None is excluded by a nonzero,
flatness, upper-boundedness or Noetherianity assumption on R'. Residue fields
are only formed at actual primes. Universe maxima cover arbitrary original
module sizes and independent ring sizes. There are no auto-bound variables.

Searches made (2026-10-24):

- Prescribed msearch LeanFinder query: "finite flat complex fibre cohomology
  concentrated degree zero arbitrary base change canonical truncation quasi
  isomorphism". Eight results, including generic `quasiIso_ιTruncLE_iff` and
  `quasiIso_πTruncGE_iff`, but no fibre criterion or universal zigzag statement.
- Prescribed msearch Loogle query: "CochainComplex.truncLE,
  ModuleCat.extendScalars, QuasiIso". Zero hits.
- Prescribed msearch LeanSearch query: "fibrewise cohomology concentration finite
  flat complex universal base change truncation". Eight generic truncation and
  geometric flatness results; none states this result.
- Prescribed msearch grep: `truncLE|fiberwise.*[Qq]uasi|fibrewise.*[Qq]uasi`
  in `Algebra/Homology`. Twenty-five reported generic truncation hits. These
  supplied the existing truncation API rather than a second truncation.
- Direct `rg` in Mathlib for `truncLE`, `mkHomToSingle`, `homologyπ`,
  `extendScalars`, `extendScalarsComp`, `mapHomologicalComplex` and residue-field
  declarations: used existing constructions as above. The composition
  comparison has same-universe ring binders, so the helper copies only its
  canonical mate expression with independent binders, not an alternative tensor.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for fibrewise/fiberwise,
  concentration, truncLE, scalar extension and this node id. The existing
  algebraic-diagonal theorem cites this as a proof input but does not state it.
  The existing general additivity theorem was found and reused. No duplicate
  name `extendScalarsCompOfUniverses` or `fibrewiseFlat_complex_concentration`
  occurred. `dag/lean_names_upstream.json` was also searched by the candidate
  names. No existing declaration states the full node.

Validation: all compilation uses the prescribed `batch2/scompile.py`, in module
mode, against the published live build. Initial import, universe and line-length
errors were repaired. Final per-file compilation is recorded by the delivery
preflight below; only the expected theorem `sorry` remains.

## Second reading by Q10

A separate manual second pass reopened the node and the complete Lean module.
The dispatcher explicitly forbids starting other agents, so this is a second
pass by the worker; the maintainer's independent delivery review remains the
independent reading. The clause mapping above was rechecked against the source.
The first draft lacked the scalar-comparison squares; those were added for both
arrows. The initial Mathlib composition comparison tied the ring universes
together, so it was replaced by the identical adjoint-mate construction at
independent universes. The first import set did not publicly expose module
abelianness; that import was added. A redundant attempted additive instance
was removed once the published general theorem was found. No mathematical
hypothesis or node statement was changed.

The final pass checked the types of the two `QuasiIso` arrows, the zero-component
quotient normalization of b, the natural-transformation domain and codomain,
the direction of the scalar comparison, and the equation determining e. In
particular e cannot be an arbitrary unrelated endpoint isomorphism: its hom
is forced by the inclusion and quotient. Both comparison squares have the
same source and target under successive scalar extension, and the helper's
data is an actual canonical isomorphism, not `Nonempty` data chosen from an
existence theorem. The seven-step natural-language proof covers the one sorry.
