## Worker report

This repairs returned immutable head `d8a8772d45f5`. The saved packet was inspected
and its prescribed initial `deliver2.py --no-push` was run before editing. Its Lean
statement still had all three H3 omissions named in the return. The module now
states `SSet.Enhanced.Operadic.operadic_correspondence_kan_filling`, with the same
mathematical statement as the current DAG node. The proof remains `sorry` only.
No mathematical definition has been replaced and no new definition node is needed.

The following is a clause-by-clause reading of the node and the final signature.
Here A means `fiber F.parameter (stdSimplex.obj₀Equiv.symm 0)`; this is explanatory
notation in this report, not a private Lean definition.

| Node hypothesis or clause | Lean rendering and check |
| --- | --- |
| Small correspondence M over Delta^op times Delta^1, with source A and target B | `F : Correspondence.{u}`. The bundled `Family` supplies the full projection's categorical fibration, actual parameter fibers with generalized-operad axioms, and relative Segal limits. Source and target are the strict fibers at 0 and 1, not arbitrary models or unrelated equivalent objects. |
| The source meaning of stationary inert lifts: cocartesian for the full projection, inside the parameter fiber | Added `hglobal : HasGlobalStationaryInert F.toFamily`. Its fully read definition quantifies `z` and `e : Δ[1] ⟶ fiber F.parameter z`; a fiberwise inert edge must be `IsCocartesianEdge (lift F.operadicBase F.parameter) (e ≫ fiberInclusion F.parameter z)`. The fiber-operad axiom supplies existence of these inert lifts; the new hypothesis ensures their whole-family cocartesianness. It includes inert maps to arity zero. |
| Constant over [0] | `hconst : IsConstantOverZero F`; the existing predicate requires actual cocartesian zero-fiber transport by an equivalence and a normalized transport cylinder. |
| Both zero-fibers are spaces | `hzero0` and `hzero1` require `KanComplex (endpointZeroFiber F 0)` and `KanComplex (endpointZeroFiber F 1)`. Neither the whole source/target operad nor the target color category is assumed Kan. |
| Any monoidal infinity category, with no presentability assumption | `{V : SSet.{u}} [Quasicategory V]`, `q : V ⟶ monoidalSimplexBase.{u}` and `hmono : IsMonoidalInfinityCategory q`. There is no presentability, general colimit, or independent universe restriction. |
| X is an A-algebra | `X : A ⟶ V`, `hXbase : X ≫ q = fiberProjection ... 0`, and `hXinert`, preserving each `IsMonoidalInertEdge` from that fiber. Thus X is over the base and preserves inert edges. |
| For every color b of B | The `hcolim` binder ranges over `b : (targetColors F) _⦋0⦌`. Colors lie over arity [1]. |
| The active diagram J_b into A followed by X | The domain is the recorded `activeSlice F b`; the boundary equation is `rightJoinConeInclusion ... ≫ c = pullback.fst (fiberInclusion ... 0) (activeTargetSource F b) ≫ X`. This uses the actual source projection from the recorded active pullback. |
| A cocone over the specified base cocone, with apex [1] | Added `IsInducedActiveCocone F b F.operadicBase (c ≫ q)`. This is the existing general predicate instantiated with codomain the base and `H = F.operadicBase`. Its boundary, apex, and every join-simplex equation fix the canonical base cocone. In particular `orderedJoinInr ... ≫ c ≫ q` is the constant at the image of b, namely [1]. This is stronger than merely asking for active edges and is exactly the previously omitted base condition. |
| Operadically colimiting | `IsOperadicallyColimiting q c` retains both one-sided concatenation tests for every finite tuple, including the empty tuple. |
| An extension H restricting exactly to X | First conjunct: `∃ H : F.M ⟶ V, fiberInclusion ... 0 ≫ H = X ∧ ...`. |
| H is inert-preserving over the base and is an operadic left Kan extension | `IsOperadicLeftKanExtension F q H` includes `IsFamilyMap F.toFamily q H`, as well as the induced operadic colimit tests at every target color. These are bundled conclusion clauses, not omitted binders. |
| Every integer m > 0 | `∀ (m : ℕ) (_hm : 0 < m), ...`; m=1 is included, and m=0 is excluded only from this second assertion. |
| The prescribed union of A times Delta^m and M times its boundary | `h₀` has the pushout domain of `𝟙 A ⊗ₘ (SSet.boundary m).ι` and `fiberInclusion ... 0 ⊗ₘ 𝟙 _`. Thus `pushout.inl` is the A prism and `pushout.inr` is the M boundary, glued over their actual common A boundary. |
| h0 is over Delta^op | Two added premises: `pushout.inl _ _ ≫ h₀ ≫ q = fst _ _ ≫ fiberProjection ... 0` and `pushout.inr _ _ ≫ h₀ ≫ q = fst _ _ ≫ F.operadicBase`. A map from a pushout is over its canonical base precisely when these equations hold on the two pieces. They constrain maps on all simplices, not only vertices. |
| Its A times Delta^m restriction is a simplex of the source algebra category | Added `∀ t : (Δ[m] : SSet.{u}) _⦋0⦌, IsLaxMonoidalInfinityFunctor (fiberProjection ... 0) q (lift (𝟙 _) (SSet.const t) ≫ pushout.inl _ _ ≫ h₀)`. This existing predicate is the over-base/inert-preservation predicate for arbitrary simplicial sources and does not require A to be monoidal. The source algebra category is full, so the full-prism base equation plus these vertex conditions is exactly the simplex condition. |
| For each proper boundary face sigma, its M times sigma restriction is a simplex of E_M(V) | Added `∀ t : (SSet.boundary m).toSSet _⦋0⦌, IsFamilyMap F.toFamily q (lift (𝟙 _) (SSet.const t) ≫ pushout.inr _ _ ≫ h₀)`. Together with the entire-boundary base equation, vertexwise membership is equivalent to every face being a simplex of the full family-map subcategory `familyMaps F.toFamily q`. Higher coherence is already present in h0 itself; no discretization of the boundary is made. |
| The restriction to M times {0} is an operadic left Kan extension | Added `∀ t : (SSet.boundary m).toSSet _⦋0⦌, (SSet.boundary m).ι.app _ t = stdSimplex.obj₀Equiv.symm 0 → IsOperadicLeftKanExtension F q (lift (𝟙 _) (SSet.const t) ≫ pushout.inr _ _ ≫ h₀)`. For m>0 the boundary contains the initial vertex; its inclusion is injective, so this selects its unique lift and is not vacuous. No extra initial-vertex choice is supplied as data. |
| Extension h is a simplex of E_M(V) | Added `h ≫ q = fst _ _ ≫ F.operadicBase` and `∀ t : (Δ[m] : SSet.{u}) _⦋0⦌, IsFamilyMap F.toFamily q (lift (𝟙 _) (SSet.const t) ≫ h)`. These are the all-simplex base equation and vertexwise membership in the full algebra functor category. |
| Exact prescribed restriction on both pieces | The final two equations restrict h along `𝟙 _ ⊗ₘ boundary.ι` to `pushout.inr _ _ ≫ h₀`, and along `fiberInclusion ... 0 ⊗ₘ 𝟙 _` to `pushout.inl _ _ ≫ h₀`. These are equalities, not equivalences or unspecified homotopies. |
| Boundary is the union of proper faces; no further colimits | Mathlib's `SSet.boundary` consists of nonsurjective simplices and `boundary_eq_iSup` identifies it with the union of proper maximal faces. Only `hcolim` supplies colimit existence. |

Dependency declarations used (all read with signatures and docstrings):

- `Sheaf.CategoryTheory.OperadicCorrespondence`: `Correspondence`, `Family`,
  `fiberInclusion`, `fiberProjection`, `IsFamilyMap`, `familyMaps`,
  `IsConstantOverZero`, `endpointZeroFiber`, `targetColors`, `activeSlice`,
  `activeTargetSource`, `activeSliceDiagram`, `activeSliceToTarget`,
  `IsInducedActiveCocone`, `IsOperadicallyColimiting`,
  `IsOperadicLeftKanExtension`, in `SSet.Enhanced.Operadic`.
- `Sheaf.CategoryTheory.MonoidalInfinityCategory`: `monoidalSimplexBase`,
  `IsMonoidalInfinityCategory`, `IsMonoidalInertEdge`,
  `IsLaxMonoidalInfinityFunctor`, in `SSet.Enhanced`.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`: the existing
  fibration/strict-fiber/cocartesian-edge interface and `cocartesianFibrationOver`.
- `Sheaf.CategoryTheory.OperadicActiveIncidenceComparison`:
  `SSet.Enhanced.Operadic.HasGlobalStationaryInert`, reused rather than copied.
  Its already-landed owning node is added to `stmt_deps` under the explicit
  stage-2 authorization to cite landed helpers. Its statement/proof dependencies
  do not depend on this item. The theorem in that module is not a hypothesis here.
- Mathlib's cartesian product `lift`, `fst`, tensor of maps, limits `pushout`,
  `pushout.inl`, `pushout.inr`, `SSet.const`, `SSet.boundary`, standard simplices.

The three retained dependency-node copies are unchanged from the current shared
records, including their `lean` fields. No dependency module is repaired in this
round. The live correspondence source was also read with
`scompile.py --source Sheaf.CategoryTheory.OperadicCorrespondence`; it agrees with
the local side-source interface. No direct Git command or live-file write was used.

Edge cases were checked before editing. Empty active slices are retained: their
cone apex and full base remain fixed by `IsInducedActiveCocone`, so an arbitrary
apex of arity other than one cannot witness `hcolim`. Arity-zero inert lifts are
covered by `HasGlobalStationaryInert`; the zero fibers alone are Kan. Noninvertible
arrows in the target color infinity category are allowed. For m=1 the boundary is
the two vertices, so the initial-vertex hypothesis applies and both endpoint maps
are family maps; the counterexample in the return no longer supplies arbitrary
h0 data to an unconditional extension claim. In particular its composites through
the zero-arity endpoint object need not preserve inert edges (a noninvertible
zero-arity-to-color edge over an inert base arrow is not cocartesian). For every
positive m the initial vertex belongs to the boundary (`boundary_obj_eq_univ 0 m`),
so the conditional quantification specifying that vertex is nonvacuous. No initial
Kan condition is silently moved to the other endpoint. h0's source restriction need
not be the X used in the first existence clause. A single universe u is explicitly
bound, as in the dependency interfaces; `autoImplicit` is false.

Searches: the saved node retains its LeanFinder, Loogle, LeanSearch and source-grep
results. This repair additionally ran `msearch.py` LeanFinder with "Existence and
relative boundary extension for operadic left Kan extensions along an infinity
operad correspondence" (eight hits, all ordinary Kan extensions or strict Segal
right Kan extensions, none this theorem); Loogle with
`IsOperadicLeftKanExtension, IsFamilyMap` (zero hits, unknown identifier in Mathlib);
and grep with `operadic.*[Kk]an|[Oo]perad.*correspondence|familyMaps` (zero Mathlib
hits). Direct `rg` in `lean/Sheaf` and `WeilConjectures` found the existing
correspondence interface and, crucially, `HasGlobalStationaryInert` in
`OperadicActiveIncidenceComparison.lean`. It found no independent existing theorem
of this statement. The boundary API and the existing family-map/full-subcomplex
implementation were read to check the vertexwise translation. No helper definition
was duplicated. The cited source passages were reopened: GH Definitions
A.3.1--A.3.3 and Theorem A.3.4, and HA Lemma the project server (printed p. 347).

Return-point resolution: the three H3 issues are rendered explicitly in the table;
H8 is repaired by a docstring carrying all nine DAG proof steps, including all
source-cell cases, gluing and inert preservation, the prism filtration, inner cells,
and the last outer-horn cell. Public imports are statement dependencies; imports
also include each available recorded Lean proof dependency. The cell-presentation
and monomorphism-boundary-cells nodes currently have no Lean record to import.
There is no remaining `STATEMENT-DISPUTED` claim or correction of the node's TeX.

## Second reading by N4

This is the dispatcher's required separate self-check pass; the brief explicitly
forbids starting another agent. I opened the current node and final file and checked
them against the returned head, rather than retaining the old generic second reading.
The table above records each hypothesis and each conclusion separately, including
conditions inside bundled predicates and implications rather than claiming all are
named binders.

The old signature admitted every map from the boundary pushout: its only relative
premises were m and m>0. The repaired signature has five additional relative
premises: two whole-piece base equations, source algebra membership at every prism
vertex, boundary family membership at every boundary vertex, and the Kan condition
at the unique initial boundary vertex. I checked each pushout leg's orientation:
inl is the A prism, inr the M boundary, and both extension equations use the matching
leg. The filler now has its global base equation and `IsFamilyMap` at every vertex,
which were absent before. The full-subcategory definition of `familyMaps` makes this
exactly membership of a simplex of E_M(V), with no stronger condition on higher
transformation edges.

The old `hcolim` fixed only the source boundary and required the operadic-colimit
predicate; its apex and full base cocone were unrestricted. Instantiating the
recorded `IsInducedActiveCocone` with the base itself fixes all join simplices and
the apex, including when the active slice is empty. The old `F.fiberOperad` supplied
only fiberwise inert lifts; the final `hglobal` references the recorded predicate
for the full product projection. Its parameter-edge component is stationary because
the edge is mapped out of the strict parameter fiber. This is precisely the node's
family convention and is not another arbitrary lift requirement.

The existence conclusion still fixes X exactly. Its over-base and inert-preserving
clauses are inside `IsOperadicLeftKanExtension`; they were checked by unfolding that
recorded definition on paper. Neither presentability nor Kan-ness of the color
category is introduced. The nine numbered proof paragraphs were compared in order
with the node's nine `proof` records. The Lean record's `statement` is extracted
verbatim from the theorem keyword through the text immediately before `:= by`.

Validation: prescribed `scompile.py N4 lem-coef-operadic-correspondence-kan-filling
lean/Sheaf/CategoryTheory/OperadicCorrespondenceKanFilling.lean` completed with exit
code 0 and no error or warning. The sandbox file took 17.7 s and the library-shaped
file 20.8 s. The exact final signature equals `lean.statement`; line-width and
explicit-universe/`autoImplicit false` checks pass, and the file has one `sorry`,
in this node's theorem, with no new definition or postponed auxiliary theorem.

The final-packet dry run caught one docstring-style warning (an extra blank line
before the closing delimiter). It was removed without changing the signature.
The subsequent compile of the final docstring and statement completed with exit
code 0 and no warnings. Both the sandbox-shaped and library-shaped files compiled.
