## Worker report

The module `Sheaf.Paper.CompletedFrameGenericComparison` states
`AlgebraicGeometry.ProEtale.CompletedFrameGeneric.completed_frame_generic_comparison`.
Its proof is `sorry`; all helper definitions contain actual data or explicit predicates.
The mathematical statement, proof and proof dependencies of the node are unchanged.
The statement dependencies include the norm-continuous coefficient notation, the
internal/sectionwise module equivalence and the canonical continuous-function comparison.
Return H2 is repaired by adding the definition ownership node
`def-sfb-normal-generic-lisse-fiber` on five unchanged existing declarations, in place
of the generic-cocycle theorem in `stmt_deps`. No dependency module is changed.

Hypotheses, with the node and source open:

- The nonempty integral scheme is `B.X` with `[IsIntegral B.X]`. Mathlib's integral
  predicate includes nonemptiness. `B : NormalTorsorBase` supplies connectedness
  (automatic for an integral scheme), local Noetherianity, `CompactSpace B.X`
  (quasi-compactness), and both `IsDomain` and `IsIntegrallyClosed` at every stalk.
  It also supplies the actual finite-etale fibre functor, a small profinite model
  `B.pi` of its automorphism group, and the algebraically closed geometric point `B.x`.
- `B.X.functionField` is the stalk at the generic point. The binders `ks`, `Field`,
  `Algebra`, and `IsSepClosure` specify the chosen separable closure. The tower
  `B.X.functionField -> ks -> B.Ω`, `IsAlgClosure ks B.Ω`, and `hx` specify precisely
  the geometric generic point given by an algebraic closure containing `ks`.
- `q` is specified by `hq`: its value on each automorphism is the existing
  `Scheme.FiniteEtale.galoisToFundamentalGroup` for any extension to the algebraic
  closure. The path is `eqToIso (congrArg Scheme.FiniteEtale.fiber hx.symm)`.
  Neither surjectivity nor continuity of `q` is assumed; the normal generic-point
  theorem supplies them in the intended proof. This is a normalization of the
  canonical map, rather than an arbitrary homomorphism.
- `A : Type u`, `[NormedField A]`, and `hA : forall x y, norm (x+y) <= max (norm x)
  (norm y)` specify the multiplicative absolute value and ultrametric inequality.
  There is no completeness, nontrivial valuation, characteristic or local-field
  assumption on `A`.
- `NormContinuousLisse A B.X` uses the recorded all-continuous condensed ring and
  its existing pullback to the small pro-etale site, with the recorded internal
  lisse-module predicate. `F : NormalGenericLisse.FiberFunctor B.X A ks` with
  `hF : F.IsNormalized` is the landed interface to the actual generic section
  space, its scalar action and its Galois action. It introduces no alternate
  fibre: `F.sections` identifies it with `NormalGenericLisse.geometricSections`.
  Existence and rank identification are the preceding generic-cocycle node.
- `n : Nat` and `b : Module.Basis (Fin n) A (F.functor.obj L).obj.V` specify the
  chosen finite basis. On an integral normal Noetherian scheme its size is the
  constant rank by the preceding node's `RankAssertions`; thus the formulation
  does not impose an extra positive-rank restriction.

Each conclusion clause:

- `completed B.X A L` is the existing `normContinuousExtension` along
  `Completion.coeRingHom` and `Completion.continuous_coeRingHom`. This is ordinary
  `Mod.extendScalars`, not completion of a module or a derived extension.
- `IsLisseCoefficientModule ... (completed ...)` gives lisseness. The following
  pro-etale `Scheme.Cover` and local isomorphisms to `Mod.finiteFree ... n` give
  exactly rank `n`, with the same small-site inverse image.
- The existential `hN` and `hC` assert nonarchimedeanness and completeness for
  the infimum of the left and right group uniformities. `group A n hN hC` has
  carrier `ULift (Matrix.GeneralLinearGroup (Fin n) (Completion A))`, its actual
  topological group structure, inferred Hausdorffness, and these two proofs.
  The lift only places the structural group in the existing torsor universe.
  The topology is the usual matrix subspace topology; no discrete topology is used.
- `Frame` is the actual isomorphism type from the Mathlib free module on the
  lifted finite set to the restriction of the actual module to the slice site.
  `sectionModule` is the recorded internal/sectionwise functor, not a copied
  module construction. `e U` identifies `P(U)` with these actual frames.
- `P : ContinuousRightTorsor ...` supplies sheafness, local nonemptiness and
  the right-torsor axioms. `IsFramePresentation` imposes restriction compatibility
  on every slice object by its columns. Its second clause says the column of
  `e (p*g)` is the sum of the columns of `e p` times the matrix entries of `g`,
  tested using `ContinuousRingUniverse.comparison`. This is right precomposition,
  with the order prescribed by the node. The comparison is the fixed canonical
  comparison, not a freely chosen ring isomorphism.
- `U,t,ht,eA,s,tbar,htbar` present the geometric fibre point concretely.
  `toGeneric` is the actual internal-module inverse-image unit, followed by
  restriction along the specified lift into the generic base change of `U`.
  The `HEq` clause identifies the original frame columns with `F.sections L (b i)`.
  Both sides have definitionally identical underlying section types; `HEq` avoids
  expensive automatic reduction of those types and has exactly the ordinary
  equality content here. `column` exposes its underlying abelian section type.
- The next column equality uses the actual `Mod.extendUnitHom` for the completion
  coefficient map. It forces `e U s` to be the scalar-extended original frame.
  The equation for `tbar` is restriction along `ks -> B.Ω`. Thus
  `P.sectionToFibre B.x U tbar htbar s` is precisely the point induced by the chosen
  basis, rather than an arbitrary point of an unrelated torsor.
- `Classical.choose complete_group_torsor_monodromy` selects the correspondence
  with its full classification and field normalization, not a mere nonempty map.
  Its value at this point, evaluated on `q g`, is asserted to equal
  `(matrix ... g).map Completion.coeRingHom`. Here `matrix` is `LinearMap.toMatrix`
  of the normalized actual generic Galois action. There is no inverse on either
  side. This states the embedded generic Cech cocycle with the recorded convention.
- The next universal clause explicitly asserts triviality on `ker q`.
  `existsUnique r : B.pi -> continuous monoid hom GL_n(A)` asserts unique factorization
  and continuity together; equality of underlying matrices is faithful on GL.
- Finally every second module, every second finite basis, both factored
  representations and every rectangular `T` are quantified. The equivalence
  compares the generic and fundamental-group intertwiner equations. This includes
  all linear maps, including rectangular matrices with an empty dimension.

Dependency declarations used:

- `Sheaf.Paper.NormContinuousMonodromyData`: `normContinuousRing`,
  `NormContinuousLisse`, `normContinuousCoefficientMap`, `normContinuousExtension`.
- `Sheaf.Paper.NormalGenericLisseCocycle`: `NormalGenericLisse.genericMap`,
  `genericModule`, `geometricSections`, `FiberFunctor`, `FiberFunctor.IsNormalized`,
  now owned by `def-sfb-normal-generic-lisse-fiber`. The existence/rank/cocycle theorem
  is background for the intended proof; no value here is chosen from it.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionRingSheaf`, `sectionModuleFunctor`.
- `Sheaf.Paper.ContinuousRingUniverseRealization`:
  `ContinuousRingUniverse.comparison`, the adjoint-normalized canonical map.
- `Sheaf.Paper.FieldSeparableCechCoordinates`: `FieldSeparableCech.closureObject`
  and the fixed Cech convention; no private copy of the separable-closure object.
- `Sheaf.Paper.ContinuousRightTorsor`: `NormalTorsorBase`,
  `TorsorCoefficientGroup`, `ContinuousRightTorsor`, `sectionToFibre`.
- `Sheaf.Paper.CompleteGroupTorsorMonodromy`: `complete_group_torsor_monodromy`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` and its inverse-image
  framework: `coefficientRing`, `condensedRingObj`, `CondensedRing.upperStar`,
  `lowerStar`, `upperStarLowerStarAdjunction`.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `Mod.extendScalars` and `Mod.extendUnitHom`.
- Mathlib: `IsIntegral`, `IsLocallyNoetherian`, `IsIntegrallyClosed`, `IsSepClosure`,
  `Scheme.ProEt`, `SheafOfModules.free`, `ιFree`, `overFunctor`, `Over.map`,
  `Completion.coeRingHom`, and the usual matrix topology and finite basis API.
- Proof imports retain the recorded complete nonarchimedean matrix-group theorem,
  condensed-field continuous realization, normal-scheme Galois-inertia presentation,
  and compact-Hausdorff quotient theorem. The generic scalar-comparison proof node
  has no recorded Lean declaration in the current DAG; it is cited in the complete
  proof docstring but is not required to type this statement.

Edge cases checked mathematically before finalizing the statement: `n=0` uses the
empty free basis and trivial GL group; all column quantifiers are empty and no
positive-rank premise appears. Both empty dimensions in a rectangular intertwiner
are covered. The empty scheme is correctly excluded by integrality. Trivial norms,
positive characteristic, incomplete coefficient fields and separably closed generic
fields are admitted. `B.Ω` may be the purely inseparable algebraic closure of `ks`;
no assumption that the separable closure itself is algebraically closed is used.
The sheaf object universe is `u+1` and site morphisms are in `u`, explicitly retained
in the internal/sectionwise functor; the lift of `Fin n` accommodates that convention.

Sources read: the whole node and its dependency records, the corresponding declaration
signatures/docstrings in the live read source, and Bhatt--Scholze pp. 70--73 (in
particular 7.4.7 and 7.4.10). The arbitrary normed-field result is the agent extension
specified by the node, not attributed to the local-field theorem verbatim.

Searches actually run (recorded wrapper results in `searches.jsonl`):

- `msearch.py ... leanfinder`, query "Completing a normed coefficient field of a
  lisse pro etale module identifies generic Galois cocycle with pullback of frame
  torsor monodromy": eight hits, including Hilbert 90, free-module pullback and
  tensor Kaehler differential results; none states this comparison.
- `msearch.py ... loogle`, query `"Torsor", "Monodromy"`: zero hits.
- `msearch.py ... grep`, query
  `(frame|torsor).*(completion|monodromy)|(completion|monodromy).*(frame|torsor)`:
  zero Mathlib hits.
- `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for the frame/completion,
  monodromy and generic-fibre interfaces located the recorded dependency APIs but
  no exact existing theorem. The exact item-id search in `WeilConjectures` gave no
  result. A final namespace/declaration-name search in both trees and
  `dag/lean_names_upstream.json` gave no collision.

Validation: the full final statement compiled through `scompile.py` without errors
or warnings other than the permitted postponed-proof warning. The deterministic
kernel timeout during development was fixed by exposing abelian column types and
using heterogeneous equality between definitionally identical generic section types;
no timeout or heartbeat limit was increased. Only the named main theorem is postponed.
No mathematical node fault or disputed statement was found.

## New nodes

`def-sfb-normal-generic-lisse-fiber` owns exactly the five existing declarations
`NormalGenericLisse.genericMap`, `genericModule`, `geometricSections`, `FiberFunctor`
and `FiberFunctor.IsNormalized`, in `Sheaf.Paper.NormalGenericLisseCocycle` (all full
names have prefix `AlgebraicGeometry.ProEtale`). Its source is the Section 7.4
framework of Bhatt–Scholze, Lemmas 7.4.7 and 7.4.10, with the existing explicit
normed-coefficient interface from generic-cocycle proof steps 1 and 4–8.
It defines the actual stalk generic map, actual module inverse image, sections at
the actual separable-closure site object, a functor with additive section
identifications, and the full faithfulness/additivity/scalar/action/arrow
normalizations. It asserts no existence. Its `existing: true` record follows the
Q59 `def-sfb-field-separable-cech-nerve` precedent, with no new Lean file.

Searches on 2026-10-23: LeanSearch for generic lisse sections and normalized
Galois fibre functors gave eight general section/functor hits; LeanFinder for
generic-point lisse sections and normalized scalar/Galois functors gave eight
general scheme/function-field hits; Mathlib grep for
`NormalGenericLisse|geometricSections|FiberFunctor.IsNormalized` gave zero hits.
The exact wrapper result JSON is included verbatim in the new node's
`mathlib_searches`. The same `rg` over `lean/WeilConjectures`, `lean/Sheaf` and
`dag/lean_names_upstream.json` finds the five exact declarations only in the
existing Sheaf module; the other geometricSections name is a different interface.
A definition-node search of `dag/nodes`, and blueprint search `normalized generic`,
find no owner (zero blueprint hits); a full scan of DAG Lean records finds only
the theorem node. `blueprint_refs.py ancestor` reports None, matching the item's
existing null ancestor; the new node prepends the item to its existing via chain.
The live source was also read with `scompile.py --source`, and matches the read clone.

## Repair self-check

Return L/H2 on immutable head `a350e6418343` asked for a definition node owning
exactly these five declarations, instead of citing the generic-cocycle theorem
solely for plain definitions. This packet supplies that node and replaces only
that dependency. The original packet passed the initial dry run at
`903a31870e5`, but still lacked this requested ownership record, so it was repaired
before re-delivery. The main Lean file remains unchanged from the returned
packet. Compared with current main, the item differs only in `lean` and
`stmt_deps`; its mathematical statement, proof, and proof dependencies are unchanged.

The new TeX is checked against each of the five declarations: genericMap is
fromSpecStalk at genericPoint; genericModule is CondensedRing.upperStar;
geometricSections is the underlying abelian sheaf evaluated at closureObject;
FiberFunctor carries exactly the functor and additive equivalences; IsNormalized
has its full conjunction including the final scalar-morphism existence clause.
No normality or Noetherianity is imposed on this definition, and no existence
of a normalized datum is asserted. The completion theorem still binds F and hF
as hypotheses, so there is no theorem-based choice to justify a statement
dependency. The structural proof used to regard Spec(g) as a site endomorphism
chooses no action, functor or section group.

The new node permits rank zero, rectangular empty dimensions through its existing
representation category, arbitrary normed coefficients (including trivial norm and
incomplete fields), and an arbitrary separable closure. Integrality excludes the
empty scheme. All fields and schemes are in universe u, the abelian section fibres
in u+1, precisely as in the existing signatures. No Lean declarations, new
sorries, hypotheses or conclusion clauses were added.

Repair validation on 2026-10-23: `scompile.py Q32 lem-sfb-completed-frame-generic-comparison <main module>` compiled both the sandbox probe (5.5 s) and library module (5.4 s) cleanly. The item lean.statement was checked verbatim against its file; the new definition-node signature was checked against the live source; new-node citations exactly match stmt_deps.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
