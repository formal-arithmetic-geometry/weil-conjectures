## Worker report

Delivered statement module `Sheaf.AlgebraicGeometry.BertiniSingularLocusDimension`, with
main declaration `AlgebraicGeometry.bertini_singularLocus_dimension_lt`. Its proof is
`sorry`, as required for stage 2. The four other declarations construct, with real data,
the universal section, its zero-scheme ideal, the projection and its non-smooth subset.
These are the objects introduced in this item's own statement, not independent notions.
There are no new nodes, dependency repairs, statement corrections or disputed statements.

Source read: `literature/stacks-project/varieties.tex`, Situation 0FD3 and Lemma 0FD6
(`lemma-bertini`), including its universal-family proof. The node's proof repairs the
source's inference of smoothness from a smooth fibre outside the flat open. The Lean
statement uses the non-smooth locus of the morphism, including the zero parameter, and
its six-step proof docstring retains that repaired route.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A field k | `{k : Type u} [Field k]`. No perfectness, infinite-field, algebraic-closure or characteristic hypothesis. |
| A scheme Y smooth over k | `{Y : Scheme.{u}}`, its structure morphism `(f : Y ⟶ Spec (CommRingCat.of k))`, and `[Smooth f]`. The explicit morphism is also the input required by the recorded projective-space coordinate morphism. |
| An invertible O_Y-module L | `(L : Y.Modules) [L.IsInvertible]`, the recorded `Scheme.Modules.IsInvertible`. |
| A finite-dimensional k-vector space V of dimension r, with its specified basis | `{V : Type v} [AddCommGroup V] [Module k V]`, `(r : ℕ)` and `(b : Module.Basis (ULift.{u} (Fin r)) k V)`. A basis of this finite cardinality supplies both finite-dimensionality and dimension r; an additional finrank equality or finite-dimensional instance would repeat information. The ULift is a bijective reindexing of precisely the r specified basis vectors and allows the coordinate index type to live in universe u. |
| The k-linear map ψ into Γ(Y,L) | `(ψ : V →+ Γ(L, ⊤))` and `_hlinear`. Additivity is bundled; the displayed equation is ψ(c•v) = f.appTop((ΓSpecIso k).inv c) • ψ(v). This is exactly linearity for the canonical k-action induced by f, without assuming an arbitrary module structure on global sections or introducing a local instance into the statement. |
| The sections ψ(b_i) generate L | `hgen : Epi (L.freeHomEquiv.symm ...)`. The family sends each top-open section to the compatible global section via the existing `homOfGlobalSection` and `unitHomEquiv`. Its evaluation at the top open is ψ(b_i). The epimorphism is precisely the recorded sheaf-generation predicate, with no pointwise-surjectivity assumption on global sections. |
| The associated morphism φ to P^(r−1)_k is an immersion | The `IsImmersion` instance is on `ProjectiveSpace.homOfGeneratingSections (ULift (Fin r)) f L ... hgen`, with the very same section family. This is the dependency's coordinate morphism, and includes the empty-coordinate projective scheme when r=0. No arbitrary map to projective space is substituted. |
| Coefficient space A^r_k = Spec k[x_1,...,x_r] | `Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin r)) k))`. The map to Spec k is `Spec.map (CommRingCat.ofHom MvPolynomial.C)`. This is the exact affine spectrum specified by the node. |
| The product A^r_k ×_k Y and projections | `pullback (Spec.map (CommRingCat.ofHom MvPolynomial.C)) f`, with `pullback.fst` to coefficient space and `pullback.snd` to Y. These are the fibre-product/base-change conventions of the recorded dependency. |
| pr₂*L | `(Scheme.Modules.tensorPullback (pullback.snd ... f)).obj L`. It uses the required tensor-formula pullback rather than the older abstract pullback. Invertibility of this pullback follows from the standard pullback-of-invertible result; it is not an extra assumption. |
| The coordinates x_i | `(Scheme.ΓSpecIso ...).inv (MvPolynomial.X i)`, pulled to the product by `(pullback.fst ... f).appTop`. |
| The universal section sum x_i pr₂*ψ(b_i) | `bertiniUniversalSection f L (fun i ↦ ψ (b i))`, an actual finite sum with the coordinates just described and `Scheme.Modules.tensorSectionsUnit` for the canonical pullback of sections. |
| The universal zero scheme H_univ = Z(s_univ) | `(bertiniUniversalIdeal f L ...).subscheme`. Its ideal is `(Scheme.Modules.homOfGlobalSection _ (bertiniUniversalSection ...)).zeroLocus`, exactly the recorded zero-scheme construction for a section of the pulled-back invertible sheaf. No reduced replacement is made for H_univ. |
| The projection q | `bertiniUniversalProjection f L ...`, the zero-scheme closed immersion followed by `pullback.fst`. |
| Σ, the points with no smooth open neighbourhood for q | `bertiniUniversalSingularLocus f L ...` is the set `{h | ¬ ∃ W, h ∈ W ∧ Smooth (W.ι ≫ bertiniUniversalProjection f L ...)}`. In particular this tests q on a neighbourhood, not the smoothness of its fibre alone. |
| dim Σ < r | `topologicalKrullDim (bertiniUniversalSingularLocus ...) < (r : WithBot ℕ∞)`. Coercion of the set to its subtype gives the required subspace topology; bottom is minus infinity. |
| Consequently q(Σ) lies in a proper closed subset B of A^r | The second conjunct is `∃ B : Set (Spec ...), IsClosed B ∧ B ≠ Set.univ ∧ q '' Σ ⊆ B`. Since B is a subset of that space, `B ≠ Set.univ` is exactly properness; no nonemptiness or rational-point assertion is added. |

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` (the full
  affine-local signature and docstring were read). Smoothness of `W.ι ≫ q` is used directly,
  so the type does not need an unproved finite-presentation instance merely to name Σ.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.GeneratingSections`, specifically its epimorphism predicate for a family.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`:
  `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections`; its finite-index-set
  signature, generating-section input, construction and projection docstrings were read.
- `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`:
  `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus`, with the docstring specifying a section
  as a map from the unit and its local principal ideal.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the source was obtained with
  `scompile.py --source` because that current module is absent from the old source tree.
  Its docstring explicitly specifies `Limits.pullback`, `fst` and `snd` for scheme base
  change; these existing constructions are used here.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, its definition and docstring.
- The two scheme-convention dependencies expressly introduce no separate declaration.
  The scheme, immersion, smoothness and base-change definitions that they collect are used.
- Existing canonical section pullback, `Scheme.Modules.tensorSectionsUnit`, is read in
  `Sheaf.AlgebraicGeometry.EtaleTensorSections`. Its landed owning node,
  `lem-sc-etale-qcoherent-presheaf-functorial`, is added to stmt_deps under the rule permitting
  landed nodes. This helper is the normalized unit of the canonical tensor-pullback
  adjunction; it works for any scheme morphism, not only étale morphisms. Its full
  signature and actual construction were read. The canonical adjunction's section formula
  was also read in `TensorPullbackAdjunction`.
- Conversion from a top-open section to a compatible global section reuses
  `SheafOfModules.unitHomEquiv` and `Scheme.Modules.homOfGlobalSection` from
  `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`.

The private proof-plan imports cover the currently stated conormal and smooth-differential
lemmas, relative differentials, proper/smooth base change, the finite-type and Noetherian
facts, polynomial Krull dimension and spectrum/topological dimension comparison. The two
unstated proof dependencies `lem-zl-finite-type-fibre-image-dimension-bounds` and
`lem-zl-hypersurface-nonzero-relative-differential` have no modules to import; they remain
named in the proof docstring and unchanged proof_deps. No proof dependency is imported
through the downstream smooth-member theorem; that would create a cycle.

Edge cases checked mathematically before finalizing:

- Empty Y: the product and H_univ are empty, Σ is empty, its dimension is bottom, and B can
  be empty for every r. The coefficient space is nonempty because k is a field.
- r=0: the basis has empty index type and ψ is zero. Generation of an invertible sheaf by
  the empty family forces Y empty, so the first case applies. A^0_k is Spec k and the
  empty B is proper. No positive-r or nonempty-index hypothesis was introduced.
- r=1 and Y=Spec k, L=O, ψ(b)=1: H_univ is the zero point in A^1, q is not smooth there,
  and Σ has dimension 0 < 1. Thus the statement correctly includes the zero coefficient
  fibre even when that fibre itself is smooth over k.
- Finite fields and positive characteristic: no use of density of rational points or
  separability of an unmentioned field extension is present. The conclusion is about
  topological points and a proper closed subset, exactly as stated.
- ψ need not be injective; only the source's generation and immersion hypotheses occur.
- V has independent universe v. Scheme, field and coefficient indexing use u; ULift
  supplies the required finite index set without specializing u to zero.

Searches for an existing theorem / construction:

- `msearch.py ... leanfinder "Dimension of the non-smooth locus of the universal hyperplane
  section for an immersive generating linear system is less than the dimension of the
  coefficient space"`: 8 hits, concerning standard-smooth relative dimensions, an immersion
  coborder and an unrelated ample-set codimension lemma. None states this dimension bound.
- `msearch.py ... loogle '"bertini"'`: 0 hits.
- `msearch.py ... grep 'Bertini|singular.*locus|universal.*section' AlgebraicGeometry`: 0 hits.
- `msearch.py ... leansearch "dimension bound for singular locus of universal hyperplane
  section"`: 8 hits, on support dimensions of quotients, simplicial-set dimensions, scheme
  zero loci and constructible-set degree bounds. None states the required theorem.
- `rg` in Mathlib, `WeilConjectures` and `lean/Sheaf` for the full helper/declaration names:
  no existing declaration or name collision. Searches by Bertini, universal section,
  zero locus, section pullback and projective generating sections found the already-used
  canonical maps and `BertiniSmoothMember`, which is downstream and states a different
  conclusion. The field-valued member construction in `BertiniIrreducibleMember` is not
  the universal family over the polynomial coefficient ring.
- `grep -rn 'lem-zl-bertini-singular-locus-dimension' WeilConjectures`: no hits.

Validation: the prescribed `scompile.py Q38 lem-zl-bertini-singular-locus-dimension ...`
compiled the complete module cleanly, first as a sandbox module and then at its library
module path. Every variable and universe is explicitly bound; there are no local notations,
private copies of notions, local instances or let-binders in the theorem. The only sorry
is the main named theorem, whose source and complete six-step proof are in its docstring.

## Second reading by Q38

This is a second pass by the same worker, not a claim of independent agent review; the
prompt forbids starting other agents and reserves independent review for the maintainer.
I reopened the node and the final Lean file and checked each row above against the actual
signature and helper bodies. The final version includes `[Smooth f]`, uses the given ψ and
basis in every construction, applies `IsImmersion` to the recorded coordinate morphism,
uses the tensor pullback for the universal line bundle, and constructs the zero scheme
before defining q and its no-smooth-neighbourhood set. Both conclusions are present with
exactly the original objects. I checked the empty case and bottom-valued dimension, and
verified that the canonical scalar equation adds no condition beyond the stated linearity.
No correction to the node's mathematical statement is needed. Only lean and the permitted
addition of the already-landed canonical section-pullback node in stmt_deps change.
