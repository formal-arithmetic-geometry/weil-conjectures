## Worker report

This repairs H3 and H11 of the return of immutable head `496ad3d63a12`.
The initial required dry run of the retained packet passed (commit
`a05ec28654`), but rereading its actual signature confirmed the semantic
fault: its existential derived left adjoints had no tensor identification,
and their adjunctions had no displayed generator formulas. Comments in the
old module did not impose either condition. The repaired packet changes the
signature and the report, rather than repushing that mechanically valid packet.

`Sheaf.Paper.PointSectionsReconstruction` now states
`WeilConjectures.pointSectionsReconstruction`. Its auxiliary definition
`pointSectionsReconstructionResult` expands the two coefficient-specific
conclusions. This is a predicate packaging this node's clauses, not an
independent mathematical notion, and is listed in `lean.declarations`.
There are no new DAG nodes, dependency repairs, or statement corrections.

Hypotheses and construction data, matched to every clause of the node:

- `D : FiniteFieldDatum.{u}` supplies the fixed algebraic closure of the
  finite field, and `Spec (.of D.k)` is the point. `l`, `[Fact l.Prime]`,
  and `hl : l ≠ D.p` render the prime and characteristic condition.
  `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` render the finite coefficient extension.
  `n` and `hn : 1 ≤ n` give the positive finite level. The quotient
  `Padic.coefficientExtensionRing l E n` uses the recorded valuation ring
  and its chosen uniformizer; no replacement quotient is introduced.
- `integral : Bool` ranges over exactly the two alternatives in the
  statement. The existing `PointDerivedHom.coefficientRing` and
  `coefficientSheaf` give the lifted finite ring and its constant sheaf
  for `false`, and the lifted valuation ring and the actual completed
  integral coefficient sheaf for `true`. `coefficientMap` is the identity
  at finite level and the constant-to-completion limit map integrally.
  Both coefficient-module carriers have universe `u+1`; the small site
  still has object universe `u+1` and morphism universe `u`.
- The integral module ring is represented by `ULift O_E`. This is only
  the existing canonical coefficient lift, as in the finite branch:
  `ULift.ringEquiv` identifies it with `O_E`, including its scalar action.
  Restriction along that ring equivalence is an equivalence on modules
  of the same carrier universe. Thus finite generation, projectivity,
  cohomology, and bounded representatives have exactly the same meaning.
  Integral sheaves remain modules over the completion, throughout.
- `L` is ordinary extension on modules, not a derived left-adjoint witness.
  `hobj` identifies its value on every module with the existing
  `PointDerivedHom.extensionObject`, which is precisely
  `SheafOfModules.changeOfRings` applied to `constantModules`.
  `constantModules` is the associated sheaf of the constant module
  presheaf, and change of rings is the sheafification of the sectionwise
  tensor `B(U) ⊗_{underline R(U)} underline M(U)`.
  `hmap` fixes every module-map image to the recorded
  `extensionMorphism`, conjugated only by `hobj`. That morphism is
  change of rings of the actual constant-module morphism, hence `id ⊗ f`.
  These equalities specify the construction on objects AND morphisms.
- `adj` is its abelian adjunction with the actual `sections` functor.
  `hexplicit : PointDerivedHom.ExplicitAdjunction ... L hobj adj`
  imposes BOTH formulas, not just existence of an adjunction. Its first
  conjunct is `adj.homEquiv M V h x = h_s(generator M s 1 x)`.
  Its second conjunct is
  `((adj.homEquiv M V).symm f)_U(generator M U b x)
  = b • V.val.map (toFinal ... U.unop).op (f x)`.
  The existing `generator` transports the actual sheafified pure tensor
  `b ⊗ x` through `hobj`; `toFinal` is the site's canonical final-object
  map. These are precisely the node's forward and inverse formulas over
  every object `U`. Passing this specified construction and explicit
  adjunction as data follows the node's instruction “Use their explicit
  adjunction”; it asserts no existence of an unrelated left adjoint.
- The four preservation instances express the node's assumption that
  these actual ordinary extension and sections functors are exact.
  In particular extension exactness is now present, not just sections
  exactness. `hsections` is bijectivity of the actual constant-value
  scalar map at the final object, i.e. the specified `Γ(s,B)=R`.
  Additivity is derived inside the result predicate from
  `adj.left_adjoint_additive`; it is not an additional assumption.

The conclusions are matched as follows:

- Every extension in the conclusion is `L.mapDerivedCategory`, the
  recorded localization of termwise `L` on complexes. Every sections
  functor is similarly the termwise localization of `sections`.
  Every unit and counit is specifically
  `adj.mapDerivedCategoryAdjunction.unit` or `.counit` from the recorded
  exact-functor derived adjunction. There is no existential derived
  functor or independently chosen derived adjunction remaining.
- For `integral = false`, the first conjunct quantifies over
  `(DerivedCategory.pointFiniteCohomology (ULift A_{E,n})).FullSubcategory`.
  This is bounded cohomology with finite underlying modules, exactly
  the finite branch's hypothesis. Its unit is `IsIso`, and its extension
  satisfies the existing `intrinsicFiniteTorsionConstructible` predicate.
  The second conjunct states `IsIso` of the actual counit for every
  target satisfying that predicate, so only constructible targets are
  included.
- For `integral = true`, a `Finset ℤ` outside which all homology objects
  are `IsZero` expresses bounded cohomology; `Module.Finite` in every
  degree expresses finite generation over the lifted valuation ring.
  For every such `c` the actual derived unit is `IsIso` and
  `L.mapDerivedCategory.obj c` is `sfIntegralConstructible`.
  The same conjunct supplies a cochain complex `P`, two integral
  bounds, `P.IsStrictlyGE` and `P.IsStrictlyLE`, every term finite and
  projective, and `Nonempty (c ≅ DerivedCategory.Q.obj P)`.
  These are the bounded finite-projective representative clauses of
  `DerivedCategory.IsPerfectRingComplex`, written out so the same `P`
  occurs in the following constructibility clause for
  `L.mapDerivedCategory.obj (DerivedCategory.Q.obj P)`.
  Applying the functor and its canonical representative comparison to
  the displayed isomorphism identifies this with the extension of `c`.
  Its last conjunct is the actual derived counit isomorphism for every
  `C : sfIntegralConstructibleCategory ...`.
- Naturality in both arguments is intrinsic to the actual unit and
  counit natural transformations of `adj.mapDerivedCategoryAdjunction`.
  This also includes arbitrary derived morphisms and inverses of
  quasi-isomorphisms; it is not naturality only on chosen representatives.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteCoefficientPoint`: the fixed point and its
  `pointFibreBaseIsAlgClosed`; its public dependencies supply
  `FiniteFieldDatum`, the finite-cohomology predicate, finite and
  integral constructibility, and the completed coefficient sheaf.
- `Sheaf.Paper.PointDerivedHomEvaluation`:
  `PointDerivedHom.coefficientRing`, `coefficientSheaf`, `coefficientMap`,
  `constantModules`, `extensionObject`, `extensionMorphism`, `generator`,
  `sections`, `scalar`, `finalObject`, `toFinal`, and `ExplicitAdjunction`.
  Only these real definitions are used, not its derived-Hom theorem.
  Its landed node `lem-pod-point-derived-hom-evaluation` is added to
  `stmt_deps` to cite these existing helpers. A read-only traversal of
  all of its statement/proof dependencies found no path back to this
  item (616 reachable nodes), so this reuse adds no dependency cycle.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` and
  its public tensor modules supply the recorded sheaf tensor and
  change-of-rings construction used by those helpers.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` supplies the
  actual limit lift used by `coefficientMap` in the integral branch.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.SfIntegralConstructible`:
  `sfIntegralConstructible`, `sfIntegralConstructibleCategory`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, whose witness is expanded.
- `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`:
  `CategoryTheory.Adjunction.mapDerivedCategoryAdjunction`, the
  canonical exact termwise derived adjunction.

Edge cases checked: `n=1` is admitted; `n=0` is excluded exactly by the
source's positive-level hypothesis. The zero complex, zero modules,
empty cohomological support, and zero finite-projective terms are all
admitted. Torsion finitely generated integral cohomology is admitted
(the conclusion is a finite-projective complex, not projectivity of
its homology). Both Boolean values occur. The integral coefficient
sheaf is completed, while all tensors here are ordinary. The finite
counit does not quantify over nonconstructible objects. The adjunction
formulas are imposed for arbitrary modules and every local tensor,
including zero tensors, and not only finite-free modules.

Searches: the initial packet's recorded LeanSearch, LeanFinder, Loogle,
and grep searches found only generic constant-sheaf adjunctions, with
no exact point reconstruction theorem. During this repair:

- `msearch.py ... loogle 'CategoryTheory.Adjunction.mapDerivedCategoryAdjunction'`
  returned zero hits with an unknown-identifier diagnostic. This is
  not evidence of absence; reading the upstream source located the
  declaration in `CategoryTheory/DerivedCategory/Adjunction.lean`.
- `msearch.py ... grep 'constantSheafΓAdj|pointSectionsReconstruction|ExplicitAdjunction'
  CategoryTheory` returned six Mathlib hits, all for the generic
  `constantSheafΓAdj` API in `Sites/LocalSite.lean` and
  `Sites/GlobalSections.lean`, not this reconstruction statement.
- `msearch.py ... leanfinder` with query “Exact ordinary tensor extension
  from coefficient modules and sections reconstruct constructible derived
  complexes at an algebraically closed pro-etale point” returned eight
  results about cotangent/Jacobi–Zariski sequences (including
  `Algebra.Extension.tensorH1Cotangent` and
  `Algebra.Generators.Cotangent.exact`), none matching reconstruction.
- `rg` for `pointSectionsReconstruction|ExplicitAdjunction|extensionObject`
  in the upstream `WeilConjectures` and the published point-derived-Hom
  module found the reusable definitions in the latter and no upstream
  reconstruction declaration. Those definitions are reused rather
  than copied.

The theorem docstring retains all eight node proof steps with named
interfaces: explicit adjunction and localization, finite units and
constructibility, finite counits, the cohomology criterion, DVR/PID
finite-projective models, integral units and constructibility, integral
counits by the cone and reductions, and naturality after localization.
No statement dispute or source fault was found.

## Second reading by Q73

This is a fresh self-check with the node, the revised module, the source
sentence, and the reused helper definitions open. The dispatcher forbids
starting another agent; I do not claim an independent second worker.

H3 found in the retained packet: `∃ LF, ∃ aF` and `∃ LI, ∃ aI`
constrained neither left adjoint to tensor extension, and comments claiming
explicit maps had no effect on their Lean types. Repair: ordinary `L` is
now fixed by `hobj` to `extensionObject` on every module and by `hmap`
to the tensor extension of every morphism. I unfolded
`extensionObject`, `constantModules`, and `extensionMorphism`: these are
constant-module sheafification followed by genuine tensor change of rings,
not an arbitrary map or a mere existence choice. I then read BOTH conjuncts
of `ExplicitAdjunction`; `hexplicit` requires precisely evaluation at
`1 ⊗ x` in the forward direction and `b` times the restriction of `f x`
in the inverse direction at every site object. Every conclusion now uses
that same `L.mapDerivedCategory` and the unit/counit of
`adj.mapDerivedCategoryAdjunction`. There is no unrelated derived
adjunction left in the statement.

H11 found in the retained report: its second reading called those
existentials “exactly the extension functor” without checking an equation
or either explicit formula. This reading checks `hobj`, `hmap`, and
`hexplicit` separately, and checks that the conclusion names the canonical
derived adjunction rather than a new witness. It also notices and repairs
the formerly missing exactness assumptions for ordinary extension.

I checked every remaining clause: finite-field and coefficient binders,
positive level, both coefficient alternatives, four exactness instances,
actual scalar-map bijectivity, finite bounded-cohomology unit and
constructibility, the guarded finite counit, integral bounded finitely
generated cohomology, integral unit and constructibility, the same bounded
finite-projective `P` with a representative isomorphism and constructible
extension, and the integral constructible counit. The two natural
transformations enforce the final naturality clause on the derived
categories. The integral `ULift` is the canonical ring equivalence and
changes neither completed sheaves nor scalar actions. No additional
mathematical hypothesis, excluded case, or changed node statement was
needed for the repair.
