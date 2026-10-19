## Worker report

The module `Sheaf.AlgebraicGeometry.AlterationCoverCalculus` states
`AlgebraicGeometry.PrimeToEllAlteration.alteration_cover_calculus`, with proof `sorry`.
It defines no new notions and changes only the item's `lean` record. The statement is an
11-part conjunction; the declaration docstring reproduces all eleven proof steps, including
the finite-tree construction rather than incorrectly assuming the raw generators compose.

Source checked directly: ILO, Travaux de Gabber, Exposé II, printed pp. 25–28,
1.2.5–1.2.8, 2.2.4, 2.3.1–2.3.4. I read the PDF through a sandbox text extraction.
II 2.3.4 explicitly gives flat ordinary base change. The item's nonflat dominant integral
variant is the reviewed expansion in its own proof steps 7–8: use dominant reduction,
coreflection, residue degrees, and finite generator trees. The statement keeps that variant
and does not add flatness. No statement correction or dispute is proposed.

Hypotheses and clauses, in their order in the Lean conjunction:

1. The base is `(S : Scheme.{u}) [IsNoetherian S]`, and the prime is
   `(ell : ℕ) [Fact ell.Prime]`. `IsNoetherian` is Mathlib's compact locally Noetherian
   scheme, equivalent to a finite affine cover by spectra of Noetherian rings. All objects
   are the recorded `Alt S`, not ordinary schemes over S substituted for that category.
   Finite composition uses `I : Type w`, `[Finite I]`, `J : I → Type w'`, and
   `[∀ i, Finite (J i)]`. Both covering hypotheses use `IsCoveringFamily ell`.
   The conclusion is the covering family indexed by `Sigma J` with arrows
   `g ij.1 ij.2 ≫ f ij.1`. Its index is finite by the dependent-sum finite instance.
2. Refinement by covering families is stated with arbitrary `I`, dependent `J`, and a
   family `W : K → Alt S`, where `K : Type w''`. The two covering hypotheses describe
   the cover and its covering refinements. `Refines` says their composites factor through
   `W`; the conclusion says `W` covers. In particular, taking `W` to be the composite
   family gives composition without a finiteness restriction. This also expresses the
   coarsening consequence in proof step 6. The direction of `Refines` agrees with the
   dependency definition: the first family factors through the second.
3. A covering sieve is `R : Sieve T` with `R ∈ topology S ell T`. Its finite family has
   index `Fin n`, is covering, and has every arrow in `R`, expressed by `∀ i, R (f i)`.
   This is a contained covering family, not merely a finite set of arbitrary arrows.
4. For `f : X ⟶ T` and `g : Y ⟶ T`, the existential object `P : Alt S`, projections
   `p,q`, and `IsPullback p q f g` give the categorical fibre product. Its comparison
   `j : P.obj.left ⟶ pullback f.hom.left g.hom.left` is a closed immersion, and both
   projection equations are included. Its exact image consists of points `z` in a component
   `c` of the usual scheme fibre product for which the closure of the image of `c` in the
   common target `T.obj.left` is an irreducible component. Thus it is exactly the union
   of dominating components, not any closed subscheme of that union. Reducedness comes
   from `P : Alt S`. A reduced closed immersion with this image is the unique reduced
   induced structure, as in the recorded reduced-induced-closed-subscheme dependency.
5. For any covering family and any family of categorical pullback squares
   `∀ i, IsPullback (p i) (q i) (f i) g`, the family of second projections covers `Y`.
   This applies to the reduced dominant fibre products constructed by the previous clause
   and, by the universal property, to any isomorphic choice of them.
6. Integral change of base is quantified as `S' : Scheme.{u}`, with instances
   `[IsIntegral S] [IsIntegral S'] [IsNoetherian S']`, and
   `(a : S' ⟶ S) [IsDominant a] [LocallyOfFiniteType a] [QuasiCompact a]`.
   The original base already has `[IsNoetherian S]`. There is no flatness hypothesis.
   The existential functor `F : Alt S ⥤ Alt S'` is characterized on every object by a
   closed immersion `j X` into `pullback X.obj.hom a`, with exact image the union of
   components whose image in `S'` is dense. Since `S'` is integral, this is exactly the
   dominant-component condition. Reducedness is inherited from `F.obj X : Alt S'`.
   The second-projection equation identifies its structural map; the equation on every
   `F.map f` gives compatibility with the first projection and the original arrow. Along
   with the over-category structural equation, these determine the maps canonically.
   The final quantified implication sends every covering family to its image under `F`.
   Thus this is a canonical reduced dominant base change, not an arbitrary functor assumed
   to preserve covers or a bare existence of maps without a characterization.
7. The proper generic-degree singleton clause uses integral source and target objects,
   `IsProper f.hom.left`, `Surjective f.hom.left`, and at every generic source point
   `(f.hom.left.residueFieldMap x).hom.Finite` and
   `Nat.Coprime (f.hom.left.residueDegree x) ell`. An integral scheme has one generic
   point; these are precisely generic finiteness and the prime-to-ell generic degree.
   The conclusion is `IsCoveringFamily ell` for the singleton indexed by `Fin 1`.
   These clauses concern arrows between objects, as specified explicitly in proof step 9.
   For a standalone proper generically finite arrow to an integral Noetherian target X,
   take S = X and use its identity object and the source object in `alt/X`.
8. The proper birational singleton clause retains both integral objects and properness.
   Birationality of this morphism is written without a new definition as the existence of
   a dense open `V` of the target with `IsIso (f.hom.left ∣_ V)`. For a finite-type
   morphism of integral Noetherian schemes this is the usual birational condition.
   Surjectivity is a consequence of properness and birationality, not an added assumption.
9. Finite affine open covers have `[Finite I]`, affine underlying schemes and open immersion
   arrows for every member, and the pointwise joint-surjectivity condition. The conclusion
   is that this very family covers in the alteration topology.
10. The reduced component family is constructed existentially as `U : Fin n → Alt S`
    and arrows `f`. The equivalence
    `e : Fin n ≃ {c : Set T.obj.left // c ∈ irreducibleComponents T.obj.left}`
    ensures every component occurs exactly once. Closed immersions and the exact image
    equations `Set.range (f i).hom.left = (e i).1`, together with reducedness of the
    `U i`, specify their reduced induced closed structures. The family covers.
11. Every `T : Alt S` is asserted to satisfy `IsReduced T.obj.left`,
    `LocallyOfFiniteType T.obj.hom`, `QuasiCompact T.obj.hom`, and the generic-point
    condition. A generic point is tested by singleton closure being an irreducible component.
    The target singleton closure is then a component and the induced residue-field map is
    finite. This uses exactly the dependency's definition, without a separate local notion.

Dependency declarations inspected and used:

- `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology`:
  `AlgebraicGeometry.PrimeToEllAlteration.Alt`, `topology`, `IsCoveringFamily`, `Refines`.
  I read the complete module, including both kinds of topology generators and the generic
  conditions on objects. Its remaining generator predicates are the basis of the proof plan.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`, `IsIntegral`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian` and the finite-affine-cover
  characterization. These are inherited through the topology module.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Integral`: `IsFinite` and
  `IsIntegralHom` were inspected for the finite/integral convention dependency. The main
  signature does not separately need a finite or integral scheme-morphism predicate; its
  finite maps occur in the proof of the component clause.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks.
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic` supplies `IsPullback`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` and `IsIrreducible`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.Hom.residueFieldMap`,
  `Scheme.Hom.residueDegree`. The latter's infinite-degree default is not used as a
  replacement for finiteness: the explicit finite residue-map hypothesis remains.
- Proof-only imports include the recorded
  `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme` (whose unique reduced closed
  structure theorem was read), `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`
  (the exact recorded membership lemma), `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`
  (étale base change), and `Mathlib.AlgebraicGeometry.Limits` (scheme coproducts).
  The other available Mathlib proof dependencies are imported by these and the topology
  module. The unstated coreflection, residue-degree, generic-fibre, and finite-extraction
  proof lemmas are not necessary to type the theorem: their statements are not used as
  placeholder assumptions and no definitions or theorems from them are copied here.

Edge cases checked:

- Empty objects and empty families are allowed. No `Nonempty I` is imposed; `n = 0` is
  allowed for both sieve extraction and the component cover. A component family of an empty
  scheme is indexed by `Fin 0`. The finite affine-open clause includes the empty family over
  an empty object. Generic-point clauses are vacuous on empty sources, as in `Alt` itself.
- A nonreduced base S is allowed outside the integral base-change clause. None of the other
  clauses introduces `[IsReduced S]` or an identity object of `Alt S` that might not exist.
- Purely inseparable extensions are retained; there is no separability, invertibility of ell,
  regularity, excellence, normality, or characteristic restriction.
- Generic degree zero cannot pass the finite prime-to-prime degree test for a field extension;
  explicit finiteness excludes using `residueDegree`'s infinite-extension default.
- A proper birational identity is included; both proper and affine-open identities satisfy
  their corresponding clauses. Nonflat dominant finite-type base changes remain allowed.
- All universes are declared (`u w w' w''`) and `autoImplicit` is false. Independent index
  universes are used; only finite extracted families are encoded by `Fin n`.
- Reduced dominant parts and component subschemes are specified by closed immersion and
  exact support, so an empty, larger, nonreduced, or arbitrary map cannot stand in for them.

Searches made before writing:

- `msearch.py ... leanfinder "Dominant pullbacks of prime-to-ell alteration covers and finite
  covering refinements"`: eight ordinary scheme-cover pullback results, headed by
  `AlgebraicGeometry.Scheme.Cover.pullbackCoverOverProp`; no dominant alteration calculus.
- `msearch.py ... loogle "CategoryTheory.GrothendieckTopology,
  CategoryTheory.Precoverage.IsStableUnderBaseChange"`: ten results for generated topology
  and generic precoverage stability. The matching generated-precoverage membership result
  is already the recorded proof leaf; none states the alteration theorem.
- `msearch.py ... grep "alteration|dominantPart|IsMaximallyPrimeToEllFinite"
  AlgebraicGeometry`: one unrelated comment in Mathlib birational composition.
- `rg` in `WeilConjectures` and `lean/Sheaf` for alteration calculus, dominant parts, and the
  item id found no exact theorem. `AlterationCoverStandardRefinement` is a different result,
  requiring integral quasi-excellent base and invertible ell; I opened that module and did
  not reuse it as a purported match. Dominant-function-field and other component mentions
  likewise do not give this theorem. The upstream declaration-name table and both source
  trees contain no `alteration_cover_calculus` declaration.

Validation: the prescribed `scompile.py Q45 lem-per-alteration-cover-calculus <file>` passed
for both the sandbox probe and actual library module (3.3 s and 3.2 s), with no diagnostics.
The initial failed compile only needed explicit `Scheme.{u}` annotations in the arguments
of `irreducibleComponents`: otherwise elaboration selected the category of types before
inserting the scheme carrier coercion. No hypotheses were changed to address the diagnostic.

## Second reading by Q45

This is the author's direct-delivery self-check; the maintainer performs the independent
review. I reopened the node and the complete final signature and compared each clause with
the numbered correspondence above. Both projection equations, the exact support equalities,
the `IsPullback` universal property, component enumeration, and all covering hypotheses are
present. The base-change clause has integrality on both bases and dominance plus finite type
on the map, with no flatness. A functor with its closed-immersion comparisons describes the
actual reduced dominant operation uniquely up to canonical isomorphism. I checked the
refinement direction against `Refines` in the dependency, and allowed an independent universe
for the coarser family. The generic-field clause explicitly keeps finiteness as well as
coprimality. No mathematical mismatch or statement correction was found. No new definition
nodes or dependency interface repairs were needed.
