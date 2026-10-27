## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceQcEtaleFibreBound` states
`AlgebraicGeometry.AlgebraicSpace.exists_uniform_geometricFibre_bound` with `sorry`.
It introduces no new definition and proves nothing. The informal statement is unchanged.
The only non-Lean field change is adding the already landed definition node
`def-sfb-space-absolute-quasi-separated` to `stmt_deps`, as permitted by brief-stage2 §5.
Its declaration is used directly, not copied.

Sources read: Stacks `decent-spaces.tex`, lemma-U-universally-bounded (03JT) and
lemma-bounded-fibres (03JX), including the (eta) to (zeta) to (epsilon) to (delta)
route; `spaces-properties.tex`, lemma-characterize-quasi-separated (0AHR), especially
(1) iff (3). The latest blueprint direct-images proof (3) was also read. It currently
uses compactification and the proper-base-change/open-coefficient results; this helper
retains its accepted, historical DAG attachment and is not a blueprint unit statement.

Every hypothesis and clause is rendered as follows:

| Informal clause | Lean |
| --- | --- |
| Scheme S, with the fixed size convention | `{S : Scheme.{u}}`, with explicit `universe u` and `autoImplicit false` |
| Algebraic space X over S | `(X : AlgebraicSpace S)`; this is the existing full subcategory of fppf sheaves with representable diagonal and surjective étale atlas |
| Usual field-point atlas topology | The imported `pointTopologicalSpace` is used by the existing absolute quasi-separatedness predicate |
| X is quasi-separated in the absolute sense | `(hX : IsAbsolutelyQuasiSeparated X)`; the existing definition is the affine-test criterion of 0AHR(3), equivalent to the absolute diagonal being quasi-compact |
| Scheme U with its structure map to S | `(U : Over S)`, with scheme `U.left` |
| U is quasi-compact | `[CompactSpace U.left]`, meaning every open cover has a finite subcover |
| Map a from U to X | `(a : yoneda.obj U ⟶ X.obj.obj)`, the existing natural-transformation interface |
| a is representable étale on scheme tests | `(ha : IsEtale a)`, exactly the dependency's `IsRepresentableWith` applied to étale scheme projections |
| There is a nonnegative integer d | `∃ d : ℕ`; natural numbers encode exactly the allowed integers d ≥ 0 |
| Every geometric point, from every algebraically closed field in the scheme universe | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj)` |
| Geometric fibre is the sheaf fibre product | `∃ (F : Over S) (p : F ⟶ Over.mk s) (q : yoneda.obj F ⟶ yoneda.obj U), IsPullback q (yoneda.map p) a x`; the Yoneda presheaf of F represents the actual fibre, with both projections |
| The fibre is finite over the geometric field | `IsFinite p.left` |
| The fibre is discrete | `DiscreteTopology F.left` |
| At most d points | `Nat.card F.left ≤ d` |

The representing pullback square is equivalent to the sheaf fibre product: all four
presheaves are fppf sheaves and limits of sheaves are computed on the underlying
presheaves. It specifies the geometric fibre up to its canonical unique isomorphism,
not an arbitrary scheme or an arbitrary comparison map. The same d precedes all field
and point quantifiers. Although the existential representation suffices, every other
representing scheme has the same finiteness, topology and cardinality by this isomorphism.
A finite scheme over a field has finitely many underlying points, so the `Nat.card`
clause is a real finite cardinality bound and cannot exploit its value on infinite types.
Conversely a finite discrete étale scheme over the algebraically closed field is a
finite disjoint union of copies of that field's spectrum, so the finite-morphism clause
has precisely the intended finite geometric fibre meaning.

The opening conventions for separated, integral and open-immersion morphisms do not
impose additional assumptions on a, U or X in the node. No such assumptions are inserted
into the theorem. Their dependency modules are imported, including Integral and
ClosedImmersion. Geometric points of schemes from `def-weil-geometric-point` use
`IsAlgClosed` and spectrum maps; the same inline definition here is a Yoneda map into
the algebraic-space sheaf, with its map to S explicitly bound.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (full signatures and docstrings read at lines 36–46 and 73–76).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsSurjective`,
  `IsAlgebraicSpace`; the full defining predicates were read. The other declarations
  recorded on this dependency (small site, structure sheaf, modules and restriction)
  were read but are not needed to state this geometric assertion.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  `pointImage`, `PointRepresentative.map`; its existing `Point` and `schemePointMap`
  imports from `AlgebraicSpacePointClasses` were read too.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`, imported and used for hX.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`; their full signatures and proof docstrings were read.
  The theorem uses their underlying presheaf pullback-square interface.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; also read
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField` (346–356).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used in
  the definition of representable `AlgebraicSpace.IsEtale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `IsIntegralHom`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`. Full definitions and
  their docstrings were read. Only IsFinite appears directly in the conclusion.
- `def-weil-size-convention` is a recorded metatheoretic convention; no artificial
  coefficient or skeleton object is added to the theorem.

The stated proof dependencies are imported without `public`:
`Mathlib.AlgebraicGeometry.AffineScheme` (`Scheme.isBasis_affineOpens`),
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`,
`WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite`
(`Scheme.Hom.isLocallyQuasiFinite_of_unramified`),
`WeilConjectures.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite`
(`Scheme.Hom.hasUniversallyBoundedFibers_of_isLocallyQuasiFinite`),
`Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints`
(`Scheme.Hom.boundsFiberDegrees_iff_fieldPoints`), and
`WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
(`Scheme.Hom.etale_fibre_discrete_separable_points`). Their recorded signatures and
proof plans were read. `lem-sfb-space-qcqs-permanence` currently has no recorded Lean
module, so there is no module to import for that future proof input. It is not needed
for elaborating this statement; its six-step use remains explicit in the docstring.

Edge cases checked mathematically before writing:

- Empty U: d = 0 works, and all representing fibres are empty finite discrete schemes.
- Empty X: the existence of a forces U to be empty; geometric point quantification is
  empty. There is no Nonempty binder or positive-bound condition.
- A non-surjective chart and geometric points outside its image: empty fibres are
  allowed without selecting a point in them.
- Identity chart of Spec Ω: a one-point fibre has cardinality one. A finite disjoint
  union of r copies gives the r-point case in every characteristic.
- The chart is only quasi-compact: no affine, separated, or quasi-separated instance
  for U is required. The base S is arbitrary, with absolute rather than relative
  quasi-separatedness of X.
- Geometric fields and scheme tests use `Type u` with `Scheme.{u}`; no unrelated
  smaller field universe makes the quantification vacuous. Base maps s and all
  geometric points x are quantified, not chosen once.

Searches made (all remote searches are in the sandbox's actual search log):

- `msearch.py`, LeanFinder: “An etale morphism from a quasi compact scheme to a quasi
  separated algebraic space has uniformly bounded finite discrete geometric fibres”.
  Eight hits, including scheme `LocallyQuasiFinite`, `IsFinite`, `discrete_fiber`,
  and finite/compact fibre instances. None states the algebraic-space assertion.
- `msearch.py`, Loogle: `AlgebraicSpace, Etale`. Zero hits; the service reports
  `unknown identifier 'AlgebraicSpace'`. This was not an exact match.
- `msearch.py`, grep: `AlgebraicSpace|bounded.*[Ff]ib|[Ff]ib.*bounded`, subdirectory
  `AlgebraicGeometry`. Zero returned hits.
- `msearch.py`, LeanSearch: “uniformly bounded finite discrete geometric fibres of an
  etale chart of a quasi separated algebraic space”. Eight hits, all scheme or
  topological facts; no exact algebraic-space uniform bound.
- `rg` on `lean/WeilConjectures` for the item id and bounded/fibre terms found the
  existing scheme bounded-fibre inputs, not this statement. Direct item-id search
  also found no upstream declaration. Project `lean/Sheaf` searches found only the
  citation in `AlgebraicSpaceDenseSchemeOpen`, not a theorem stating this result.
- `rg` on project algebraic-space modules for quasi-separatedness found
  `AlgebraicSpaceAbsoluteQuasiSeparated`; its node and source criterion were read and
  reused. Searching the chosen declaration name in Mathlib, WeilConjectures and
  Sheaf found no existing declaration.

No statement dispute, source error, new node, or dependency repair is needed.
The module compiled cleanly through the prescribed scompile.py wrapper on the server
(as a sandbox file and under its actual module name). Final validation is the
prescribed deliver2.py dry run and delivery.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
