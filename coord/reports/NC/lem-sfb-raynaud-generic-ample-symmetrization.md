## Worker report

States `AlgebraicGeometry.raynaudGenericAmpleSymmetrization` in
`Sheaf.AlgebraicGeometry.RaynaudGenericAmpleSymmetrization`. Its sole theorem has
proof `sorry`; no new definition or proof is supplied. The natural-language
statement and proof plan are unchanged. The existing landed definition node
`def-sfb-semiabelian-geometric-fibres` is added to statement dependencies because
it states exactly the fibre condition already spelled out in the item.

Hypothesis and clause correspondence:

- The base is `S : Scheme.{u}`, with `[IsIntegral S]` and `[IsLocallyNoetherian S]`.
  `hS` says at every point that the actual structure-sheaf stalk is an integral
  domain and is integrally closed. This follows the normal-ring dependency's
  inline convention, with no global factoriality or regularity condition.
- `G : Grp (Over S)` provides the structure map `G.X.hom`, identity, inverse,
  multiplication and all group laws over S. `[IsCommMonObj G.X]` supplies
  commutativity. `[Smooth G.X.hom]` is smoothness. `[IsSeparated G.X.hom]` means
  the diagonal is a closed immersion. Local finite presentation and
  quasi-compactness are explicit instances; separatedness supplies the remaining
  quasi-separatedness in finite presentation.
- `hG : HasSemiabelianGeometricFibres G` is the previously landed exact predicate:
  for every algebraically closed field and geometric point, there are a split
  torus of rank `r : ℕ`, an abelian variety, its kernel square, and an fppf-locally
  surjective quotient. Rank zero is included. This uses the given group laws.
- The generic base change is
  `(Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj G`.
  Thus the field is precisely the residue field of the generic point; neither
  an algebraic closure nor an arbitrary generic field extension replaces it.
- `L` is a module on that generic fibre, `[L.IsInvertible]` asserts invertibility,
  and `hL : Scheme.Modules.IsAmple _ L` is the recorded absolute ampleness.
- `∃ (I : Type u) (W : I → S.Opens)` with `iSup W = top` gives the covering,
  and `∀ i, IsAffineOpen (W i)` asserts affineness of every member. A cover
  indexed in the scheme's point universe suffices, by choosing one neighbourhood
  per point. `Nonempty (W i) →` applies the extension conclusion exactly to
  nonempty members.
- `a : ℕ` with `1 ≤ a` is the positive integer exponent. `Q` is a module on
  `pullback G.X.hom (W i).ι`, the actual base change G_W, and `Q.IsInvertible`
  asserts that it is a line bundle.
- `jη` has source G_eta and target G_W. Its composite with the canonical open
  immersion `pullback.fst G.X.hom (W i).ι` equals the canonical generic-fibre
  map to G. Since that open immersion is mono, this equation uniquely determines
  `jη`; existence is automatic for nonempty W in the integral S. Thus this is
  the canonical generic restriction map, not an unconstrained comparison map.
- `Nonempty ((tensorPullback jη).obj Q ≅ ... )` asserts exactly the generic
  isomorphism with `(L ⊗ (tensorPullback inverse_eta).obj L).tensorPow a`.
  The inverse is `ι` of the induced generic group, so this is Sigma(L)^a.
  All pullbacks here are the recorded actual tensor inverse-image functor.
- Finally `∀ V : (W i).toScheme.Opens, IsAffineOpen V → ...` asserts ampleness
  of Q after tensor restriction to the inverse-image open of V under G_W → W.
  The existential invertibility proof is only the proof required by `IsAmple`;
  it changes no module data. The clause includes V empty and V = W itself.
  No properness of G_eta, symmetry of L, or extension of L is assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` and the canonical generic point.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain`, applied to the actual stalks.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; finite presentation includes quasi-compactness.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow`, and the scheme-module sheaf tensor.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly imports
  `Scheme.Modules.tensorPullback`, retaining its actual tensor construction.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded general tensor interface;
  the scheme-module monoidal tensor is the existing specialization, not a new tensor.
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`:
  `HasSemiabelianGeometricFibres`, read in full with its source/docstring.
- Proof imports: `WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower`
  (`Scheme.Modules.isAmple_positive_tensorPow`) and
  `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
  (`Scheme.Modules.invertible_pullback_tensor`). The other three proof dependencies
  currently have no Lean record, hence no module to import. They are proof inputs,
  not missing notions in this statement. The docstring carries all four proof steps.

Edge cases read before writing: S is nonempty by integrality; an empty cover cannot
cover it. Empty members of a cover are allowed and impose no extension condition.
Every nonempty W contains the generic point, making the factorization well-defined.
The exponent is never zero, but one is permitted. Rank-zero torus, a purely toric
fibre, the trivial group, S a field, and characteristic two all remain included.
The geometric predicate quantifies over fields in the scheme universe, following
its already reviewed interface. Relative ampleness on the empty inverse-image open
uses the existing vacuous ample condition. Neither generic properness nor a chosen
rigidification enters the signature. No statement dispute or correction was needed.

Searches for an existing exact statement:

- `msearch.py leanfinder`: "A positive power of a symmetrized ample line bundle on
  the generic fibre extends to a relatively ample line bundle over affine opens
  of a normal semiabelian base". Eight hits: affine-local ring-map properties,
  localization, normalization and limit section results. Read the returned types;
  none is this extension theorem.
- `msearch.py loogle`: `"IsAmple", "pullback"`. Zero hits.
- `msearch.py leansearch`: "Raynaud generic symmetrized ample line bundle extension
  over a normal base scheme". Eight hits, on normalization and unrelated symmetric
  forms/rays/metrics. None states a line-bundle extension theorem.
- `msearch.py grep`: `Raynaud|semiabelian|symmetri.*ample`, Mathlib AlgebraicGeometry.
  Zero hits.
- `rg` in the full `lean/WeilConjectures` and `lean/Sheaf` trees for `Semiabelian`,
  `semiabelian`, `Raynaud`, `symmetrization`, and generic-ample-symmetrization names.
  Found the shared semiabelian predicate and related different theorems, especially
  `symmetricLinePowerProlongation` (dense-open symmetric input, no ampleness output)
  and `exists_affine_cover_isAmple_of_normal_smooth_group` (arbitrary local ample
  lines with no prescribed generic comparison). Neither states this item.
  The required grep for this node id in WeilConjectures returned no hits.
- Read the predicate's node and implementation, the ten statement-dependency
  records/signatures/docstrings, and the recorded proof imports. Searches in the
  latest blueprint found no alternate exact statement; the node is an inherited
  supporting result with no blueprint-unit statement of its own.

Source check: the Moret-Bailly II 3.3.3 opening paragraph, printed p.53, was read
in the publisher-hosted scan/search extraction at
https://www.numdam.org/item/AST_1985__129__1_0.pdf . It invokes Raynaud XI.1.13 to
prolong a positive power, reducing a generic line to a difference of ample lines.
The exact symmetrization/positivity formulation remains the accepted node's
agent-formulated version, not a claim of verbatim quotation. Raynaud's book was
identified on the publisher page https://link.springer.com/book/10.1007/BFb0059504 ;
its original theorem text was not available locally. No source text was invented.

Validation: the delivered module compiled cleanly via `scompile.py`, both the sandbox
and library module checks, with no errors or warnings. All universes and binders
are explicit; `autoImplicit` is false. Only the named theorem is postponed.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
