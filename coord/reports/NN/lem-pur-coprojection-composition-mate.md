## Worker report

Repair of immutable returned head b47298149111. The initial saved packet passed the
mechanical dry run (01e652f8b6), but the required mathematical self-check found that
it still had the exact defects in the return. Those definitions and theorem binders
have been repaired; the packet is not an unchanged re-push.

`Sheaf.Paper.CoprojectionCompositionMate` now states the composition equation for
canonical components, with no arbitrary projection, adjunction, exceptional compositor,
pullback compositor, or independent data for f. All definitions have real data. The helper
`coprojectionProEtaleTensorMate_existsUnique` fixes the coordinate transport of the
explicit tensor mate. Its predicate requires HEq of the inverse datum with d and HEq
of the resulting map with the explicit upstream PF composite; it cannot select a map
by endpoints alone. It matches the node's canonical-construction clause. The main
`purityCoprojectionCompositionMate` matches the two composition equations. The further helper `coprojectionStandingKappa_existsUnique` supplies the unique
exceptional transpose characterized by `coprojectionKappaProperty`: its inverse standing
Hom image must be HEq to that exact tensor-mate composite, and its off-domain extension
is zero. Thus choosing from its existence theorem is the allowed choice from a uniquely
determined universal property. These three proofs are postponed, each with a complete
proof docstring. The tensor is the published
`derivedTensor`, and `coprojectionDerivedUnit` caches its actual monoidal unit.
`coprojectionTensorObj` is an irreducible alias for an object of that bifunctor, so
standing-domain inference does not expand K-flat total complexes. `coprojectionInverseData` caches the entire `TensorInvertibleData` type at generic
coefficient instances, including exactly that tensor and unit; `purityTensorObject` uses the frozen alias in
map endpoints. Unfolding the alias identifies them exactly.

Hypothesis-by-hypothesis correspondence:

* `P : PurityFiniteSetting` retains the fixed geometric field, the prime distinct from
  its characteristic, the finite p-adic extension, and the positive finite coefficient
  level. `purityDerived P T` uses its actual quotient coefficient ring with the standard
  lift and the small pro-etale site (object universe u+1, morphism universe u).
* The `Over`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` instances on
  X, Y, Z say exactly that they are separated finite-type k-schemes. The corresponding
  instances on f and g and their `IsOver` instances say that they are the composable
  separated finite-type k-morphisms of the node. The composite's instances are derived.
* `_hK` now uses the recorded `finiteTorConstructibleProEtaleModule` predicate, as
  required by K in Dbc_tf; the returned version had only bounded constructibility.
  `_hN` and `_hN'` impose that same recorded predicate on N and its inverse.
* `d : coprojectionInverseData (ModuleCat P.Coefficient) Z N` (definitionally the
  recorded `TensorInvertibleData` for the derived tensor and unit) is the recorded chosen inverse
  N'=d.inverse and evaluation e=d.iso. This is actual tensor-invertibility, rather than
  a free inverse object together with unrelated adjunctions. The pullback inverse for
  f is computed as `coprojectionPullbackInverse (ModuleCat P.Coefficient) g d`; no independent af is accepted.

Clause-by-clause correspondence:

* `coprojectionTensorAdjunction (purityDerived P T) d` uses upstream
  `tensorRightEquivalenceOfTensorIso (β_ d.inverse N ≪≫ d.iso) d.iso`, followed by
  `Equivalence.toAdjunction`. Its left functor is tensor by N', its right functor
  tensor by N, and its counit is exactly associator; (1 tensor e); right unitor.
  Upstream Equivalence.mk normalizes the unit while leaving this counit unchanged.
* `coprojectionPullbackInverse` has inverse Lh*N' and evaluation
  `leftDerivedUpperStarTensorIso ... .symm`, then Lh*(e), then the published
  `leftDerivedUpperStarUnitIso`. This is precisely the node's mu_h normalization.
* `purityKappa` starts with that target tensor adjunction's unit at F_h(U), where
  U=H_h(K) tensor p_h(N). Its fixed representative then applies `projectionMap` at (U,N'), tensors by N,
  applies F_h to associator; (1 tensor pulled evaluation); unitor, and finally
  tensors the standing counit by N (the inverse standing Hom bijection applied to
  the identity of H_h(K)). The generic `coprojectionTensorMate` assembles this sequence;
  `coprojectionProEtaleTensorMateRepresentative` supplies the actual PF and evaluation;
  `coprojectionProEtaleTensorMate` is its uniquely fixed coordinate transport, and
  `coprojectionStandingCounit` is the inverse standing Hom image of the identity.
  `coprojectionKappaProperty` requires the inverse standing Hom image of kappa to be
  HEq to this fixed composite. Bijectivity therefore determines exactly the displayed
  exceptional transpose in the node; `coprojectionStandingKappa` selects that unique map.
* The standing Hom equivalence only accepts the stated bounded-below etale-origin
  domain. The characterization quantifies over its proof-only domain conditions and requires
  zero outside that domain; `coprojectionStandingKappa` selects its unique witness. On every finite-Tor input of the theorem, tensor
  stability, exceptional finite-Tor preservation, and constructible etale origin
  make those tests true. This supplies no additional hypotheses and asserts no
  exceptional adjunction on an unrestricted ambient category. The extension does
  not select unspecified maps from existence statements.
* `purityExceptionalComposition P f g K` is literally
  `standingExceptionalComposition P f g ⟨K,hK⟩` whenever K is bounded constructible,
  with a zero extension off that domain. This applies to K and K tensor N here.
* `purityFinitePullbackComposition P.Coefficient f g` is the published canonical
  derived upper-star compositor, defined as a helper in the item module from
  `leftDerivedUpperStarComp`. It is induced by upperStarComp and its termwise
  K-flat derivation; it is not an endpoint isomorphism supplied by the caller.
  The unused canInv binder is removed.
* The first conjunct is κ_gf followed by c_(K tensor N), equated to
  (c_K tensor can_N), then κ_f at H_g(K) with the pulled-back inverse, then H_f(κ_g).
* The second conjunct quantifies exactly the three IsIso assumptions, defines each
  co-projection by `inv` of this very κ, and gives the node's inverse equation in
  the same composition order as the returned version.

Dependencies used: `PurityFiniteSetting` from `Sheaf.Paper.PurityFiniteSetting`;
`TensorInvertibleData` from `Sheaf.Paper.Pur9Invertible`;
`finiteTorConstructibleProEtaleModule` from `Sheaf.Paper.FiniteTorAmplitudeProEtaleModule`;
`projectionMap` and the tensor and unit comparisons from the finite-coefficient
upstream ProEtale derived modules; `standingExceptionalHomEquiv` and
`standingExceptionalComposition` from `Sheaf.Paper.StandingExceptionalComposition`;
the specified exceptional functor as the definitionally equal transported
`rightDerivedUpperShriek` from the finite-coefficient upstream module; `tensorRightEquivalenceOfTensorIso` from
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`; and Mathlib's
`Equivalence.toAdjunction`. The derived braiding is the explicit published
`DerivedCategory.braidedCategory` from
`WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided`, read through
scompile.py --source because the older source checkout lacks that module. It descends
the Koszul braiding and selects no map from a Nonempty hypothesis. `purity_coprojection` from `Sheaf.Paper.PurityCoprojection`
identifies the inverse for closed immersions in the proof plan. The fixed-scalar
pullback compositor is the helper defined in the item module from the published
upstream declaration.

Edge cases checked: identities must use the canonical compositors and the normalized
unit; there is no freely chosen zero PF for the composite. For an odd-shift invertible
object the tensor symmetry is the derived symmetry, and adjointification preserves the
prescribed evaluation counit, so the naive odd-shift sign error is avoided. Changing
N' or its evaluation changes the normalized tensor unit compatibly, as in proof step 5.
For the tensor unit the construction is the ordinary counit mate. For K=0 every map
has the appropriate zero endpoint. Empty schemes and zero coefficient objects are
not excluded by the binders; the source's tensor-invertibility condition is retained.
All universes are explicitly bound. No statement correction or disputed statement.

Searches: retained the previous search record and repeated msearch.py LeanFinder on
“Composition of canonical exceptional inverse image coprojection mates of the compact
support projection formula”: eight unrelated generic categorical hits, no match.
Loogle on `CategoryTheory.tensorRightEquivalenceOfTensorIso, CategoryTheory.Adjunction`
returned no hits because the first name is upstream, not Mathlib. Direct rg of
WeilConjectures/Mathlib/CategoryTheory/Monoidal found precisely the upstream tensor
inverse equivalence used here, and its full definition was read. msearch.py grep on
`mateEquiv.*comp|comp.*mateEquiv` in CategoryTheory/Adjunction found generic mate
composition results, no specialized theorem. rg of the upstream project and lean/Sheaf
for the item id and its declaration name found no existing declaration. The original
LeanSearch, LeanFinder, Loogle, and Mathlib grep queries remain documented by the node.

## Self-check by NN

I reread the node, its eleven proof steps, the source Step 4(ii), and the declarations
with the repaired file open. Each defect in return H3/H5/H2-H4 is addressed: no arbitrary
PF, no arbitrary exceptional or tensor adjunction, prescribed evaluation-normalized unit,
canonical c, canonical can, no unused canInv, pulled-back rather than independent f data,
and explicit tensor-invertibility. The main composition order of both conjuncts is
preserved. The main theorem docstring contains all eleven DAG proof steps and their
cited dependency nodes. The recorded pullback dependency remains unchanged; its
fixed-coefficient compositor is supplied directly by the item module as a helper.
Compilation
and the final delivery dry run are recorded below after they complete.

## Validation

Final scompile.py check of `CoprojectionCompositionMate.lean` succeeded with no errors or warnings;
the sandbox and owning library paths both compiled. The item node lists the helper
`AlgebraicGeometry.ProEtale.purityFinitePullbackComposition` alongside the other module
declarations. Every file stayed within the prescribed 60-second limit. The final source contains no diagnostic commands
or heartbeat overrides, and only the three documented theorem proofs use sorry.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
