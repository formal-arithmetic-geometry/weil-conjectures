## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.SemiabelianGenericPicardClassLifting`,
with the single theorem `AlgebraicGeometry.semiabelian_generic_picard_class_lifting`.
Its proof is `sorry`; the complete three-step DAG proof is in its docstring. The
natural-language statement, proof, and proof dependencies are unchanged. No theorem
is proved in this delivery. The additional definition module constructs the quotient
from existing notions, with no postponed data or proof inside a definition.

Hypothesis and clause correspondence:

- `S : Scheme.{u}`, `[IsIntegral S]`, and `[IsLocallyNoetherian S]` are the stated
  integral locally Noetherian base. `hS` asserts `IsDomain` and `IsIntegrallyClosed`
  on every actual stalk, exactly the specified normality convention.
- `G : Grp (Over S)` and `[IsCommMonObj G.X]` supply the addition, inverse, identity,
  all group identities, commutativity, and the requirement that operations are over S.
- `[Smooth G.X.hom]` and `[IsSeparated G.X.hom]` are smoothness and a closed diagonal.
  `[LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]` give finite
  presentation: quasi-separatedness follows from separatedness, so no condition is
  missing from the finite-presentation convention.
- `hG : HasSemiabelianGeometricFibres G` is the shared exact-fppf geometric-fibre
  condition: kernel the split torus, fppf-locally-surjective quotient to an abelian
  variety, rank `r : ℕ` allowed to be zero. Its existing definition uses all
  algebraically closed fields of the scheme universe and all maps from their spectra.
- `S.fromSpecResidueField (genericPoint S)` fixes eta and its actual residue field K.
  `pullback.snd G.X.hom ...` is the structure map of the actual generic fibre.
- `α : Scheme.Pic.GeometricQuotient ...` ranges over the full Picard quotient.
  It is not a representative line with an added symmetry or positivity assumption.
- `∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W` gives precisely an affine neighbourhood
  of the arbitrarily supplied point `s`.
- The existential `a` with `ha : a ≫ W.ι = S.fromSpecResidueField ...` is the unique
  factorization of the canonical generic map through that open. It exists because
  a nonempty open of an integral scheme contains its generic point; its uniqueness
  follows from the open immersion being mono. Thus this introduces no additional
  hypothesis or choice of generic point/field extension. Both `Over.homMk` objects
  are explicit to avoid unresolved pullback endpoint inference.
- `n : ℕ`, `0 < n` is the node's integer n at least one, with no bound fixed to two.
- `M : (pullback G.X.hom W.ι).Modules`, `hM : M.IsInvertible` is the actual line
  module on G_W. `Scheme.Pic.ofIsInvertible` passes to its isomorphism class.
- `baseChangeMap G.X.hom (Over.homMk ... a ha)` is the canonical map G_eta -> G_W.
  `Scheme.Pic.map` is the existing inverse-image map on invertible isomorphism
  classes. Its upstream implementation is the existing adjoint pullback;
  the project identifies it with tensor inverse image by its adjunction. This
  delivery introduces neither another pullback functor nor an arbitrary map.
- `geometricClass ... (...) = α ^ n` is equality only after quotienting by
  geometric algebraic triviality. Multiplicative notation is tensor addition,
  so `α ^ n` is exactly n alpha. There is no isomorphism to a tensor power of a
  chosen representative asserted. The elementwise positive-multiple condition
  is also exactly the stated torsion-cokernel formulation: the union of the local
  images is a subgroup, by tensoring/dualizing after restriction to a common affine
  neighbourhood. The explanatory equivalence is recorded in the proof docstring,
  without adding a tautological second conjunct or replacing the local assertion.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with
  `IsDomain` on stalks, following def-weil-pbc-normal-ring's inline convention.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`;
  `Morphisms.FiniteType`: `LocallyOfFiniteType`, `QuasiCompact` (also in the shared
  family and geometric-fibre definitions).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` and the existing scheme module tensor.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded general tensor interface;
  scheme modules retain the existing specialization of the same localization tensor.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionAdjunction`, and its
  composition interface, publicly imported by LineAlgebraicEquivalence.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: base change is the
  existing `pullback` with its projections, and `baseChangeMap` from PicardFunctor.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, with its
  actual algebra map, field and algebraic-closure instances, all in universe u.
- Added existing definition-node dependencies `def-sfb-semiabelian-geometric-fibres`,
  `def-sfb-line-algebraic-equivalence`, and `def-sc-picard-group` point to, respectively,
  `HasSemiabelianGeometricFibres` in SemiabelianGeometricFibres,
  `Scheme.Modules.AreAlgebraicallyEquivalent` in LineAlgebraicEquivalence,
  and `Scheme.Pic` in WeilConjectures.AlgebraicGeometry.PicardFunctor. The group
  structure, `Pic.map`, and `Pic.ofIsInvertible` are publicly provided by
  WeilConjectures.AlgebraicGeometry.Picard.Group; no Picard group is redefined.

Proof-only imports include InvertiblePullbackTensor, Proper, Smooth and
QuasiSeparated for the recorded pullback/base-change proof inputs. The two
biextension proof dependencies have no recorded Lean statement on the read base;
they are not needed to type this theorem and cannot yet be imported. They are
preserved verbatim in proof_deps and fully named in the proof docstring.

Edge cases: S is nonempty by integrality, so no generic point of an empty scheme
is invented. W cannot be empty since it contains s. The group of dimension zero,
the trivial line/class, abelian varieties (torus rank zero), split and nonsplit
tori, varying torus ranks, imperfect fields, and characteristic 2 are not excluded.
No separability or invertibility of n in the base is assumed. A same-universe
algebraic closure exists, so no independent smaller-universe quantifier becomes
vacuous. The new quotient construction also makes sense for an empty X and
requires no representable Picard functor. Closure of the geometric zero set
changes no equivalence relation: tensoring a generating family with a fixed line
preserves it, as does taking duals; the trivial line supplies the identity.

Searches: msearch.py leanfinder, query “Local rational lifting of generic Picard
classes modulo geometric algebraic equivalence on a semiabelian scheme”, returned
ring Picard groups and elliptic-curve point classes, not the statement. Loogle
`Picard, Semiabelian` found no identifier Picard. Mathlib grep
`Semiabelian|NeronSeveri|AlgebraicEquiv` in AlgebraicGeometry found no matches.
Additional leansearch and leanfinder searches for the geometric Picard subgroup
returned CommRing.relPic and related ring results; whole-Mathlib grep
`AlgebraicallyTrivial|GeometricPicard|NeronSeveri` found none. The exact timestamped
responses are recorded in searches.jsonl and in the new node's mathlib_searches.
`rg` over WeilConjectures and Sheaf found and led to reuse of Scheme.Pic,
AreAlgebraicallyEquivalent, and HasSemiabelianGeometricFibres. The precise item id
has no upstream occurrence. DAG definition-statement search found no node for the
geometric Picard quotient; other occurrences are theorem statements using it.
`tools/blueprint_refs.py search` for “geometric algebraic equivalence” and
“geometric Picard quotient” gave zero nodes. `ancestor` returned None, as already
noted in the accepted split; the new node preserves that null ancestor and via chain.

The current blueprint direct-images proof (3) was read. It has only the global
constructibility context, not this supporting quotient assertion. Milne AV I §8
and the Néron–Severi paragraph preceding Remark 10.19 were read from the local
PDF. Raynaud and Moret-Bailly originals are locally missing as the existing node
already records; this delivery makes no claim to have read them or to transcribe
their theorem. No source-based statement correction was necessary. No
STATEMENT-DISPUTED flag is raised.

Validation: both modules compiled separately in dependency order through scompile.py;
all variables and universes are explicit. Only the item's named theorem has sorry.
The first theorem elaboration required explicit source/target Over objects in
Over.homMk; that was repaired and both files then compiled cleanly.

## New nodes

`def-sfb-geometric-picard-quotient` owns
`Sheaf.AlgebraicGeometry.GeometricPicardQuotient`, with `geometricAlgebraicZero`,
`GeometricQuotient`, and `geometricClass` in `AlgebraicGeometry.Scheme.Pic`.
It constructs the subgroup generated by classes whose actual tensor pullback to
AlgebraicClosure k is related to the unit by the existing smooth-connected-family
relation. Tensor/dual stability makes that precisely the geometric zero subgroup;
`Subgroup.closure` supplies actual subgroup data without postponing any proof.
The ordinary group quotient and its natural class map are real constructions.
The source convention is the item's explicit geometric definition, compared with
Milne I §8 and Remark 10.19's Picard quotient. This is not the ring-theoretic
relative Picard kernel or a new version of ordinary algebraic equivalence. The
searches above found neither a definition node nor a Lean declaration for it.

Dry-run repair: the recorded main signature was initially truncated at a named-argument
assignment. It is now copied through the actual theorem proof delimiter; the Lean source
was unchanged. New-node citations were separated into individual bracketed identifiers.

## Second reading by Q85

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
