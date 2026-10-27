## Worker report

Q53, stage 2, 2026-10-22, item `lem-sfb-inertia-free-finite-cover-coarse`.
The module `Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse` states
`AlgebraicGeometry.inertiaFreeFiniteCoverCoarse`, with its entire proof postponed by
`sorry`. The companion definition module contains three fully written predicates.
No theorem is proved and no definition has postponed data or a postponed proof.
The item's statement and six-step proof are unchanged. Its only field changes are
`lean` and the addition of the definition node to `stmt_deps`.

The preceding worker's supersession note concerns stage 1. I opened the accepted
Q63 report, which expressly says “Stage 1 only”, and the current node, which has
`status: split` and no `lean`. This delivery preserves that accepted split and
supplies stage 2; it does not split the node again.

Hypotheses and clauses, in order:

- The field is `(k : Type u) [Field k]`. The base is exactly `Spec (.of k)`.
- The two stacks over k are total categories `X` and `Y` over `Over (Spec (.of k))`.
  `hX : IsDeligneMumfordModuliStack X` includes stack descent, representable
  algebraic-space diagonal, and a surjective etale scheme atlas. `hY : IsModuliStack Y`
  expresses the node's assumption that Y is a stack, before its DM property is deduced.
- Finite type of X is `hft : HasFiniteTypeEtaleModuliAtlas X`: a surjective etale
  atlas U with `LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom`. For a DM stack over
  a field, this is the standard finite-type atlas criterion. It includes
  quasi-compactness, not merely local finite type. No chosen atlas is an input.
- Finite diagonal is `hdiag : HasFiniteModuliDiagonal X`. Each two-scheme test
  has an actual representing scheme Z and its two actual maps p and q; finiteness
  is `IsFinite (prod.lift p q).left` over the product in `Over S`, namely T ×_S U.
  It is not finiteness of either projection and is not only finiteness of inertia.
  The comparison of the first projection is a `ModuliTwoIso`; that of the second
  is a natural isomorphism of total functors whose components lift identity base
  arrows, so it also identifies the projection over the base.
- The specified coarse scheme is `(Q : Over (Spec (.of k)))`, its map is
  `(q : BasedFunctor X (discreteModuli (yoneda.obj Q)))`, and its universal property
  and geometric isomorphism-class bijection are exactly the existing
  `hq : IsCoarseModuliScheme X Q q`. I use that recorded definition unchanged.
- The given finite representable morphism is `(ν : BasedFunctor Y X)` and
  `hν : IsRepresentableFiniteModuliMap ν`. For EVERY scheme test T and t to X,
  this gives Z finite over T, an equivalence to `moduliTwoFiberProduct t ν`,
  and a `ModuliTwoIso` identifying its first projection with the given finite map.
  Reversing the two factors relative to Y ×_X T only uses symmetry of the 2-product.
- Every algebraically closed field extension, including its specified map to k,
  is quantified in `hgeom` by Ω, `[Field Ω]`, `[IsAlgClosed Ω]` and
  `a : Spec (.of Ω) ⟶ Spec (.of k)`. Every object is
  `y : Functor.Fiber Y.p (Over.mk a)`. Triviality of its automorphism group is
  `∀ (α : y ≅ y), α = Iso.refl y`. A scheme map between spectra of fields is
  precisely a field-extension map in the reverse direction, so no separate
  choice of an unrelated extension map appears. The universes agree with the
  recorded stack and coarse-moduli conventions; the stack total categories
  retain independent explicit object and morphism universes v₁,w₁,v₂,w₂.
- “Y is represented by an algebraic space” is the first conjunct: an actual
  `E : AlgebraicSpace (Spec (.of k))` and a based functor from its discrete
  moduli category to Y whose total functor is an equivalence.
- Finiteness of THE composite is the second conjunct,
  `IsRepresentableFiniteModuliMap (ν.comp q)`.
- The final clause is an actual k-scheme `Z : Over (Spec (.of k))`, an actual
  k-map `g : Z ⟶ Q`, and `IsFinite g.left`. The equivalence
  `e : BasedFunctor (discreteModuli (yoneda.obj Z)) Y` and
  `ModuliTwoIso (e.comp (ν.comp q)) (discreteModuliMap (yoneda.map g))`
  make this a representation over Q of the originally specified composite.
- There is no assumption of linear reductivity, tameness, characteristic,
  flatness, local finite presentation of ν, nonemptiness, or surjectivity of ν.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsModuliStack`, `IsDeligneMumfordModuliStack`,
  `IsCoarseModuliScheme`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`,
  `discreteModuli`, `discreteModuliMap`, `ModuliTwoIso`, `HasSpaceBaseChange`,
  `SpaceMapIsEtale`, and `SpaceMapIsSurjective`. Their signatures and docstrings
  were read, including their total-category and projection conventions.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`, reusing its affine
  and finite-on-sections condition. The dependency's `IsIntegralHom` was read
  in `Morphisms.Integral`; the item uses only its finite clause.
- The algebraic-space type is the existing `AlgebraicGeometry.AlgebraicSpace`
  of `Sheaf.AlgebraicGeometry.AlgebraicSpace`, publicly supplied by the moduli
  framework. The source definition and its representable-property predicates
  were read. The finite scheme maps are not replaced by arbitrary space maps.

The proof docstring reproduces all six accepted DAG proof steps and names their
nodes. Plain proof imports include the three already available inputs:
`Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable`,
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`, and
`WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`.
The other four proof-only stack theorems currently have no Lean record, so they
are not falsely imported or restated. They introduce no object needed to TYPE
this statement. The schemehood and representable-sheaf declarations were opened;
the final Mathlib leaf is `AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`.

Sources opened: `stacks-more-morphisms.tex`, `theorem-keel-mori` (0DUT), whose
conclusion is separated, quasi-compact and universal homeomorphism, not
representable finite; `algebraic.tex`, `lemma-algebraic-stack-no-automorphisms`
(045H); `stacks-morphisms.tex`, `definition-locally-finite-type` and
`definition-quasi-compact`; and `spaces-morphisms.tex`, `definition-integral`
(03ZP), including its finite clause and scheme-test discussion.

Edge cases checked from the definitions and hypotheses: the empty source and
empty atlas are permitted; no cover is required to be surjective except the
atlas. If X is a scheme and q its identity, the statement specializes to the
specified finite scheme morphism. If X = BG for a finite constant group and
Y = Spec k, the atlas is finite and the resulting map to its coarse Spec k is
finite even when the group order equals the characteristic. Thus no tame or
linearly reductive hypothesis enters. Non-DM examples such as B(mu_p) do not
satisfy `hX`. The automorphism condition retains actual automorphisms and does
not replace groupoids by their isomorphism classes. Nonreduced test schemes
are included in both finite predicates and in the conclusion.

Searches were executed through the prescribed unmodified `msearch.py`:

- LeanFinder, “An inertia free finite representable cover of a finite type
  Deligne Mumford stack is finite over its coarse moduli scheme”: eight hits,
  all scheme finiteness or scheme finite-fibre facts; none states the stack result.
- Loogle, `"AlgebraicGeometry", "IsFinite"`: twelve scheme-property hits;
  reuse `IsFinite` but no duplicate of this assertion.
- LeanSearch and LeanFinder, “Representable finite morphisms of stacks and
  finite diagonal with finite type etale scheme atlas”: eight hits each,
  scheme representability, scheme finite/type properties, and generic relative
  representability; none gives these predicates for the recorded total categories.
- Mathlib grep, `CoarseModuli|DeligneMumford|RepresentableFinite|FiniteDiagonal`
  in `AlgebraicGeometry`: zero hits.
- `rg` with the same names in the specified `lean/WeilConjectures` and
  `lean/Sheaf` trees: the moduli framework and unrelated coefficient/tower
  Cartier-diagonal declarations; no finite stack-test predicates. The exact
  item-id search in `WeilConjectures` had no hit.
- Whole-DAG `rg -l 'finite diagonal|representable finite' dag/nodes` found
  theorem users but no definition of the missing predicates. In particular
  `def-sfb-diagonal-coefficient-finite-diagonal` concerns Cartier classes.
  `blueprint_refs.py search 'finite stack'` found zero hits; search
  `'finite diagonal'` found two unrelated cohomological/Cartier entries.
  `blueprint_refs.py ancestor` returns None, retained in the new node.

The new node retains the search outputs verbatim in `mathlib_searches`. No
statement correction or `STATEMENT-DISPUTED` is needed. No repair note for this
item was found. Both modules compiled cleanly via `scompile.py`, individually
in dependency order (10.1s and 11.3s for the library checks).

## New nodes

`def-sfb-finite-stack-scheme-tests` defines the missing scheme-test predicates
`CategoryTheory.IsRepresentableFiniteModuliMap`, `HasFiniteModuliDiagonal`,
and `HasFiniteTypeEtaleModuliAtlas` in the single module
`Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`. It is built from the recorded
moduli, algebraic-space, scheme, etale, finite-type, fibre-product and finite-map
notions. Its source is the representable scheme-test convention, the stack
finite-type/atlas criterion of Stacks Morphisms of Stacks, and 03ZP for finite
space morphisms. The searches above rule out an existing definition node or
Lean declaration. Each predicate has real, explicit Prop-valued data, no choice,
no axiom and no `sorry`. The item cites the new node in `stmt_deps`.

## Second reading by Q53

This is a second pass by the same dispatched worker; no independent reader or
sub-agent was started, as instructed in the dispatcher brief. The maintainer's
independent review remains the review of this delivery.

I reopened the node and both Lean files after compiling. Each hypothesis and
each of the three conclusion clauses is matched above. In particular, I checked
that the diagonal is finite over T ×_S U; that both projections are compared
over identity base arrows; that representable finiteness retains its projection;
that the finite-type atlas includes quasi-compactness; and that the final
representation is over Q via an isomorphism of the specified composite. No
redaction of the mathematical statement was required. During this pass I
corrected the definition module's source tag to 03ZP after checking the local
tag table and reading its finite clause. This changed docstrings only. The
three definitions contain no postponed proof, and the only theorem has proof
`by sorry`. All variables and universes are explicitly bound; every Lean line
has at most 100 characters.

Dry-run repair: the first server preflight rejected the new node's combined
`[def-sfb-stable-pointed-moduli-groupoids, def-trf-algebraic-space]` citation,
because its dependency-citation checker requires a separate bracket for each
id. I split those into two individual citations without changing the statement.
I also read `stacks-properties.tex`, `lemma-quasi-compact-stack` (04YC): a
quasi-compact stack admits a quasi-compact scheme atlas, obtained by a finite
open subcover of any smooth atlas; the same open-subcover argument preserves
etaleness for a DM atlas. This verifies the finite-type atlas encoding over k.
The new node's source record now names this criterion explicitly.
