## Worker report

The new module `Sheaf.AlgebraicGeometry.KernelIdealDirectedPairs` states
`AlgebraicGeometry.Scheme.CommAlgebraSheaf.kernelIdeal_directed_pairs`, with one
`sorry` and no definitions or proofs. The node is unchanged except for `lean`.
There are no new nodes, dependency repairs, statement corrections, or disputed
statements. No repair note exists for this item.

Read the item, all five statement dependencies and their recorded declarations,
and all three proof dependencies and their full statements and source docstrings.
Read Stacks `properties.tex`, the proof of
`lemma-algebra-directed-colimit-finite-presentation` (05JS, especially the pair
relation at lines 3318–3337), and
`lemma-integral-algebra-directed-colimit-finite` (0817, especially the lifting
square in part (2), starting at line 3424).

The mathematical objects are encoded as follows. The supplied ideals and the
constructed generated ideals use exactly the representation of the existing
kernel-image-ideal node: module sheaves with sectionwise injective maps whose
ranges are ideals. `Scheme.IdealSheafData` represents ideals of the structure
sheaf; the present ideals are in arbitrary algebra sheaves `S_i`, so that API
would not apply. No substitute ideal-sheaf definition is introduced. Minimality
specifies the generated ideal uniquely as a subsheaf; the quotient is specified
by its kernel and its algebra universal property, not as an arbitrary algebra.

Hypothesis-by-hypothesis correspondence:

- `X : Scheme.{u}`, `[CompactSpace X]`, `[QuasiSeparatedSpace X]` are precisely
  the scheme and qcqs assumptions.
- `I : Type u` with `Preorder`, `Nonempty`, and `IsDirected I (· ≤ ·)` is the
  small nonempty directed preordered set. Indices are in the objects' universe,
  following the existing finite-presentation Hom-colimit interface.
- `S : I ⥤ X.CommAlgebraSheaf` supplies the algebra objects, all transition
  maps, and their identity and composition laws. `hS` is quasi-coherence of
  every underlying module, precisely the recorded algebra definition.
- The ideal sheaf `J_i` is `(c i).pt` with inclusion `j i`. The family `J i U`
  consists of section ideals. `hJ` says that the inclusion is injective on
  every open and its range is this ideal. `hJqc` is its quasi-coherence.
- `hσ` says on every open that each transition sends `J_i` into `J_i'`.
  Because the inclusions are module morphisms and injective, this is exactly
  containment of ideal subsheaves; it also determines the induced module map.
- `K i : Type u`, with its `Preorder`, `Nonempty`, and `IsDirected` instances,
  is the nonempty directed preordered row index set.
- `E i : K i ⥤ X.Modules` supplies each row's modules and compatible transitions
  `η`. The dependent instance binder is
  `SheafOfModules.IsFinitePresentation.{u} (R := X.ringCatSheaf) ((E i).obj k)`
  for every `i,k`. Its Mathlib docstring defines precisely local cokernels
  of maps between finite free module sheaves; it does not assume projectivity
  or finite presentation only on global sections.
- `c i : Cocone (E i)` supplies the compatible `ε_ik = (c i).ι.app k`.
  `hc i : IsColimit (c i)` is the module-colimit universal property with
  vertex `J_i = (c i).pt`. There is no colimit assumption in algebra sheaves.

Clause-by-clause correspondence of the construction and conclusion:

- `Σ i : I, K i` is exactly the pair set `P`. It belongs to `Type u`, so its
  smallness is expressed by the type itself, without a cardinal bound.
- The existential families `M`, `m`, and `L` give the generated ideal
  subsheaves. The first conjunct identifies the ideals `L p U` with the
  section ranges of the inclusions. The second contains the image of
  `(c p.1).ι.app p.2 ≫ j p.1`. The third says these ideals are contained in
  every ideal subsheaf containing that image, on every open. This is exactly
  the node's smallest sheaf of ideals, not the potentially smaller presheaf
  of sectionwise generated ideals on nonaffine opens.
- `∃ pairOrder : Preorder (Σ i : I, K i)` supplies the preorder structure.
  Its very next conjunct characterizes its order by the required equivalence:
  `p ≤ r` iff there is `h : p.1 ≤ r.1` and the corresponding `S.map (homOfLE h)`
  sends `L p` into `L r` on every open. Thus this is the specified relation.
- `Nonempty` and `IsDirected` for this pair order assert the node's
  nonemptiness and directedness, not antisymmetry.
- `Monotone (fun p ↦ p.1)` is monotonicity of projection.
- The next clause is `k ≤ l → (i,k) ≤ (i,l)` for each row.
- The extension clause quantifies every `i ≤ i'` and `k : K i`, and produces
  `l : K i'` with `(i,k) ≤ (i',l)`.
- `Q : P ⥤ X.CommAlgebraSheaf` supplies the quotient objects and transitions,
  including the functor laws. Each object is required to have quasi-coherent
  underlying module. Equivalently this is a diagram in the full subcategory
  `QuasiCoherentAlgebra X`; no algebra or transition is changed.
- `q p : S.obj p.1 ⟶ Q.obj p` is the quotient map.
  Its sectionwise ring kernel is `L p U` on every open. The following unique
  factorization clause states the universal property for every algebra map
  killing `ε(E)`. Together with generated-ideal minimality, this is exactly
  the algebra sheaf quotient by the generated ideal: killing the image is
  equivalent to killing its generated ideal. It identifies the sheafified
  sectionwise quotient canonically up to the unique isomorphism preserving q;
  there is no unjustified sectionwise-surjectivity assertion on all opens.
- Finally `q p ≫ Q.map f = S.map (homOfLE h) ≫ q r` is precisely
  `α_(r,p) q_p = q_r σ_(r.1,p.1)` in categorical composition order.
  It holds for every arrow `f : p ⟶ r` and proof `h : p.1 ≤ r.1`.
  Projection monotonicity guarantees such `h`; the preorder is thin, so all
  choices of its proof give the same transition.

Declarations used from the statement dependencies:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category.
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`:
  `Scheme.CommAlgebraSheaf`, its `toModule`, and
  `Scheme.IsQuasiCoherentAlgebra` / `QuasiCoherentAlgebra`. The theorem writes
  the defining module predicate rather than replacing it by another notion.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  is transparently `SheafOfModules`; the established `Scheme.Modules` is the
  same specialization `SheafOfModules.{u} X.ringCatSheaf`, including morphisms.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone` and `IsColimit` render
  the colimit dependency. Their full definitions were read in `Cones.lean`
  and `IsLimit.lean`, as was the generated `colimit` definition's source.
- The convention node has no declaration of its own. Its qcqs conventions
  are the Mathlib topological classes written explicitly above.

All recorded proof-dependency modules are imported privately:
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
(`Scheme.Modules.quasicoherent_finite_type_affine`),
`Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal`
(`Scheme.CommAlgebraSheaf.generated_ideal_quotient_quasiCoherent`), and
`Sheaf.AlgebraicGeometry.FinitePresentationHomDirectedColimit`
(`Scheme.Modules.hom_directedColimit_of_isFinitePresentation`). The docstring
reproduces all four proof steps, their uses, and the quotient functor-law argument.

Edge cases checked before writing: empty X; zero E or J; generated ideal zero
or the whole algebra and hence zero quotient; singleton row and outer sets;
preorders with distinct mutually comparable equal-stage representatives;
arbitrary noninjective S and E transitions. The hypotheses allow every case.
Empty index sets are excluded precisely where the node excludes them. In the
zero-ideal case the pair relation reduces to the outer order and is indiscrete
inside each row, which is correctly a preorder. No reducedness, Noetherian,
finite-type-algebra, faithful-map or injective-transition assumption is present.

Searches actually run with the prescribed `msearch.py` wrapper:

- LeanFinder: "Directed pairs of generated kernel ideal sheaves form a directed
  preorder with a diagram of quotient quasi-coherent algebras". Eight hits,
  including normalization diagrams, `Scheme.IdealSheafData` lattice instances,
  directed affine covers, and locally directed open-cover colimits; no match.
- Loogle: `CategoryTheory.IsFiltered, Preorder`. Seven hits including
  `IsFiltered.isDirectedOrder`, `isFiltered_of_directed_le_nonempty`, and
  sequential-functor declarations; only the general order/filtering interface.
- Grep: `IdealSheaf|idealSheaf|generatedIdeal|ideal.*[Dd]irected`, under
  `AlgebraicGeometry`. Twenty-five hits, mostly `Scheme.IdealSheafData` and
  its comap and subscheme interfaces; no arbitrary-algebra pair construction.
- LeanSearch: "Generated ideal quotients in a diagram of quasi coherent sheaf
  algebras indexed by directed pairs". Eight hits, including
  `localCohomology.ringModIdeals`, quasicoherent presentation data, and ring
  quotient algebra maps; none states this sheaf-algebra pair theorem.
- `rg -n 'kernelIdealDirected|generatedIdeal|generated_ideal|KernelIdealDirected'`
  on `lean/WeilConjectures` and `lean/Sheaf` found only the existing generated
  ideal quotient theorem, which is retained as a proof dependency.
- The prescribed recursive search for the exact item id in
  `lean/WeilConjectures` found no declaration.
- A final exact-name search for `kernelIdeal_directed_pairs|kernelIdealDirectedPairs`
  in Mathlib, `WeilConjectures`, and `Sheaf` found no collision.

Validation: `scompile.py Q142 lem-weil-pbc-kernel-ideal-directed-pairs` compiled
this file in both sandbox mode (19.7 s) and actual library module mode (13.0 s),
with no errors or unexpected warnings. All variables and the single universe
are explicitly bound. There are no local notations, private helpers, instances,
`let` binders, `show` terms, or data chosen from postponed existence proofs.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
