## Worker report

The delivery states `AlgebraicGeometry.ProEtale.affineProperSquare_stratifiedModule` in
`Sheaf.Paper.AffineProperSquareStratifiedModule`. Its proof is `sorry`, with all six
DAG proof steps in the declaration docstring. The only definition,
`affineProperSquareBaseChangeMap`, is the actual canonical map from
`(P ×_T T') ×_T U` to `T' ×_T U`, constructed by `pullback.lift` with the
first projection followed by `P ×_T T' → T'` and the second projection to `U`.
Its compatibility proof is an application of the existing associativity and
pullback-condition equalities; no new theorem is proved and no data is postponed.

The node's statement, dependencies and proof are unchanged. No new definition node,
dependency repair, statement correction or disputed statement is needed.

### Hypotheses and clauses

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The positive-characteristic field is
  `(k : Type u) [Field k] [Fact (ringChar k).Prime]`, and the different-characteristic
  condition is `[Fact (ringChar k ≠ ℓ)]`. A field has positive prime characteristic
  exactly when its ring characteristic is prime.
- The precise finite-subextension condensed algebraic closure is
  `Profinite.padicAlgClRingObj ℓ`, the underlying abelian ring object of the recorded
  `padicAlgClCondensedRing`. `condensedRingObj ... X` is `p_X^*` of that ring.
  It is not the discrete constant ring or all continuous functions into Qbar.
- `P T T' : Scheme.{u}` and `t : T ⟶ Spec (.of k)` provide all structure maps:
  those on `P` and `T'` are `p ≫ t` and `h ≫ t`. Finite type of `T` is
  `[LocallyOfFiniteType t] [QuasiCompact t]`. Properness is `[IsProper p]`.
  The quasi-compact locally closed immersion is `[QuasiCompact h] [IsImmersion h]`.
  Mathlib's `IsImmersion.isImmersion_iff_exists` identifies this with exactly a
  closed immersion followed by an open immersion. Neither absolute separatedness
  of `P` nor absolute separatedness of `T` is assumed.
- `N : Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u+1}) (...)` is an internal module.
  Every restriction uses the existing exact `CondensedRing.upperStar` along the
  indicated scheme morphism, hence uses the coefficient-cartesian identification.
- The given Zariski-local finite partitions are explicitly supplied by the open
  cover `V : I → P.Opens`, its coverage equation `hV`, and
  `L i : Scheme.FiniteLocallyClosedStratification (V i)`. The independent universe
  `v` permits arbitrary cover index sets. This is the given local stratification
  data, not a global constructibility hypothesis.
- `hN` says for each local stratum there exists a pro-etale scheme cover `C` on
  which the inverse image along `C.f z ≫ (L i).immersion c ≫ (V i).ι` is
  `Mod.IsFree`. The latter means isomorphic to `Mod.finiteFree ... r` for some
  natural `r`, exactly local finite freeness, with no uniform or positive rank.
- `U : T.Opens` and `hU : IsAffineOpen U` quantify over every affine open.
  `P_U = pullback p U.ι`, `T'_U = pullback h U.ι`, and
  `P'_U = pullback (pullback.snd p h ≫ h) U.ι`, literally using `P' = pullback p h`.
- The first four conjuncts give `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact` for each of these four corners' displayed maps to `Spec k`.
  These are exactly the standing separated finite-type scheme hypotheses.
  The next two conjuncts are properness of `pullback.snd p U.ι` and the canonical
  `affineProperSquareBaseChangeMap p h U`. The next three give
  `IsLocallyNoetherian P_U`, `CompactSpace P_U`, and `QuasiSeparatedSpace P_U`.
  CompactSpace here means quasi-compact, with no Hausdorff assumption.
- The universal refinement clause takes every finite cover `W : Fin n → P_U.Opens`,
  affine-open proofs `_hW`, and its coverage equation `_hcover`. Subordination to
  the given local stratifications is the chosen assignment `a : Fin n → I` and
  the actual inclusions `q j : W j ⟶ V (a j)` with equation `_hq` over `P`.
  These are simply the supplied subordinate-cover data; no extra module condition
  is imposed on the charts.
- The conclusion supplies `S : Scheme.FiniteLocallyClosedStratification P_U`.
  This recorded structure supplies finite locally closed disjoint images covering
  `P_U`, their scheme representatives, immersions and range equalities. The first
  additional clause explicitly gives `Topology.IsConstructible (S.stratum b)`.
  Mathlib's predicate is the finite Boolean/locally-closed description with
  quasi-compact open parts requested by the node.
- For each `b` the next clause supplies `j`, `c`, and an actual morphism
  `r : S.domain b ⟶ pullback ((L (a j)).immersion c) (q j)`.
  Its equation `r ≫ pullback.snd ... ≫ (W j).ι = S.immersion b` expresses
  factorization through a stratum of the restricted stratification. The local
  representative is its fibre product with `W j`, not an arbitrary subscheme
  with the same image, and the assertion is stronger than mere image containment
  in precisely the way the node requires.
- The next clause gives a pro-etale cover of each `S.domain b` on which the
  inverse image of `N` along the composite to `P` is `Mod.IsFree`. Composition
  comparisons identify this with the stated inverse image of `N|P_U`.
- The following clause states `IsLocallyFinitelyPresented` for the inverse image
  on the same stratum, over `condensedRingObj ... (S.domain b)`.
- Finally, `boundedConstructible (...) ((DerivedCategory.singleFunctor _ 0).obj
  ((CondensedRing.upperStar ... (pullback.fst p U.ι)).obj N))` is membership of
  the degree-zero restricted module in the full ordinary bounded constructible
  derived category. This is the general internal-module predicate publicly retained
  by the recorded dependency module, not its discrete-coefficient specialization.
  Its ordinary ambient morphisms impose no completeness or perfectness condition.

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`,
  `Scheme.proetalePrecoverage` and `Scheme.Cover`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `padicAlgClSubfunctor`, `padicAlgClRingObj`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing` and `condensedRingObj` (same pulled-back ring, bundled/unbundled).
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`.
- `Sheaf.Paper.CartesianCoefficients`: `cartesianCoefficients`,
  `cartesianCoefficientLift`, `cartesianCoefficientPullbackIso`; the inverse images
  used are `CondensedRing.upperStar` from the publicly imported upstream framework.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from the morphism quasi-compactness module.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` and `IsSeparated`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  their composite notion is Mathlib `IsImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the setting documented there and in `CondensedRing.compactificationOverField`
  is explicitly rendered by the corner conclusions; no compactification is needed here.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, used for both local and global partitions.
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` publicly retains
  the general `AlgebraicGeometry.ProEtale.boundedConstructible` and
  `BoundedConstructible` from
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
- Existing proof notions are `Mod.IsFree`, `Mod.finiteFree`,
  `Mod.IsFinitelyPresented` in `WeilConjectures.CategoryTheory.ModuleObjects.Free`,
  and `IsLocallyFinitelyPresented`, `IsConstructibleModuleObject` in
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`.
  Because the first and the local-presentation predicate occur in the public signature,
  their imports are public as well. All recorded available proof dependency modules
  are imported; unavailable proof nodes are not restated or assumed.

### Source and edge-case checks

Read the Stacks source statements and proofs of composition/base change of finite
 type, finite-type Noetherianity, and composition/base change of proper maps in
`literature/stacks-project/morphisms.tex`. Read Bhatt--Scholze Definitions 6.8.3,
6.8.6 and 6.8.8 directly from the PDF via pdftotext: local finite freeness, finite
stratifications with lisse restrictions, and bounded cohomology in the full ordinary
derived category. Read the current blueprint unit `sk-thm-sf-package/_section.md`.

Empty `P_U` admits `n=0` and zero global strata; the factorization clauses then have
empty domains. No type is required Nonempty, and no rank is required positive.
Nonempty `P_U` cannot admit an empty covering by its coverage equation. Empty local
or global strata are retained and do not force a positive rank. `Mod.IsFree` includes
rank zero and allows a different finite rank on every covering member. A zero module
therefore meets the hypotheses, as does the empty scheme. Affine localization only
concludes separatedness after localization: the affine line with doubled origin as
base, with `p` the identity, is not excluded. Independent cover-index universe `v`
and small pro-etale site object/morphism sizes are unchanged.

### Searches actually run

The `msearch.py Q105 lem-sf-affine-proper-square-stratified-module` log records:

- LeanFinder: `Affine proper square global immersed refinement of locally stratified
  finite free internal pro etale modules and bounded constructible degree zero complex`.
  Eight hits, including `IsImmersion.isImmersion_iff_exists` and etale/ideal-sheaf
  declarations; no theorem states this node.
- Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.LocallyOfFiniteType`.
  Seven hits, including `IsProper.toLocallyOfFiniteType` and `isProper_iff`;
  these are geometric ingredients, not this combined assertion.
- Mathlib grep: `IsLocallyFiniteFree|IsLocallyFree|LocallyFiniteFree`.
  Five hits, all the sectionwise `SheafOfModules` notion. We use the existing
  `Mod.IsFree` and scheme covers directly rather than define a second notion.
- LeanSearch: `Global finite immersed stratification of pro etale locally finite
  free internal modules on affine proper squares`. Eight hits about immersions,
  proper maps and sectionwise presentations; none is this assertion.
- Project rg over `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `IsLocallyFiniteFree|IsLocallyFree|LocallyFiniteFree`, and the proposed declaration
  names. The local-free encoding theorem and recorded internal-module definitions
  are available, but no combined affine-square/global-refinement theorem or name clash.
  DAG search for local finite freeness found the consumer and related comparison
  nodes, no definition requiring a new record. The exact source-id search found
  no declaration for this item. The compact-object example was opened; its current
  file is withdrawn and contains no declarations.

### Validation

`scompile.py` compiled the module in sandbox mode and library-module mode cleanly.
Initial elaboration failures were repaired by opening the existing ring-object
instance scopes, using named implicit arguments of `pullback.condition`, and annotating
`pullback p U.ι : Scheme` when it appears as an underlying topological space.
The last source change made the two signature dependency imports public; the dry run
recompiles that final version. No global build, live file edit or direct git command
was run. The maintainer performs the independent review under the current dispatcher
contract; no second reader or independent review is claimed in this worker report.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
