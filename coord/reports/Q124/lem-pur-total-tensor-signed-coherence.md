## Worker report

The delivery states `CategoryTheory.RingedDerivedNative.totalTensor_signed_coherence`
in `Sheaf.Algebra.Homology.TotalTensorSignedCoherence`. Its conclusion is the explicit
Prop structure `TotalTensorSignedCoherence` specialized with
`(A := RingedDerivedNative.Modules J R)`. The single theorem has proof `sorry`.
Every other declaration has fully written data: one composite of existing isomorphisms,
three predicates describing summand formulas on arbitrary chain maps, sixteen named clauses of
the statement, and the conjunction structure. These are helpers belonging to this node,
not additional mathematical notions or assumed comparison maps. They are all recorded in
`lean.declarations`. The predicates and canonical shift composite are written generically over the
module category A and its existing tensor structures, then specialized only in the
theorem. They assert nothing for arbitrary A: the only postponed theorem is about
the required ringed-site module category. This removes repeated elaboration of the
large sheaf-tensor instance without changing the statement or splitting the module.

Hypotheses and objects, matched to the node:

- A ringed site: `{C : Type c} [Category.{v} C]`, `J : GrothendieckTopology C`, and
  `R : Sheaf J CommRingCat.{max c v u}`. Commutativity is in `CommRingCat`.
- Small relative to ordinary module sheaves: the section universe is `max c v u`;
  both site object and morphism sizes fit, with no equality between `c` and `v` imposed.
  The `HasSheafify` and `WEqualsLocallyBijective` instances express the ordinary
  sheafification infrastructure used by the existing native tensor. They hold in this
  small-site setting and are not flatness or boundedness hypotheses.
- Module sheaves: the existing `RingedDerivedNative.Modules J R` is exactly Mathlib's
  `SheafOfModules` on the underlying ring sheaf, hence definitionally the category
  `ringedSiteModules` recorded by `def-weil-sheaf-of-modules-category`.
- Arbitrary, possibly unbounded complexes: every complex variable has type
  `CochainComplex (Modules J R) ℤ`, without an amplitude or flatness predicate.
- All shifts, homogeneous degrees, and total degrees have type `ℤ`, including negative
  values. The shifts `⟦a⟧` are the recorded Mathlib convention with term `E.X (p+a)`
  and differential `a.negOnePow • d`.
- `⊗` is the existing complex monoidal tensor, definitionally
  `CochainComplex.mapBifunctor E F (curriedTensor _)`. It is the direct-sum total
  with signs `ε₁=1`, `ε₂(p,q)=(-1)^p`, not a derived tensor or chosen replacement.

Each conclusion clause is rendered as follows (field names refer to the conclusion
structure; their named predicates contain the full displayed formulas):

- `totalTensorShiftIso` (with A specialized to `Modules J R`) really constructs the isomorphism by
  `mapBifunctorShift₂Iso (E⟦a⟧) F ... b`, then the `b`-shift of
  `mapBifunctorShift₁Iso E F ... a`, then `(shiftFunctorAdd ... a b).app ... |>.symm`.
  Thus it is exactly `s¹_a[b] ∘ s²_b`, including the canonical addition-of-shifts map.
- `shift_formula` states coefficient `(b*p).negOnePow` after precomposing
  the chain map with `HomologicalComplex.ιTensorObj (E⟦a⟧) (F⟦b⟧) p q n h`.
  Its right side is that scalar times the inclusion of the component tensor in
  degrees `p+a,q+b` and total degree `n+(a+b)`. Shifted component objects are
  definitionally the unshifted components at those indices. This is an equality
  of module-sheaf morphisms, expressing the formula on every component tensor.
- `associator_formula` uses the actual `(α_ E F G).hom`. It precomposes with
  the inner inclusion whiskered by `G.X r`, then the outer inclusion. The result
  is the ordinary module-sheaf associator followed by the other two inclusions.
  The ordinary associator sends `(x tensor y) tensor z` to `x tensor (y tensor z)`.
- `symmetry_formula` uses the actual `(β_ E F).hom`. Its composite with the
  `(p,q)` inclusion equals `(p*q).negOnePow` times the ordinary module-sheaf
  braiding followed by the `(q,p)` inclusion. The ordinary braiding swaps pure tensors.
- The isomorphism types give chain maps and actual two-sided inverses, rather than
  existence of an unconstrained map or a `Nonempty` choice.
- `shift_inverse` explicitly assigns `(b*p).negOnePow` to the reverse reindexing;
  its input summand has unshifted degrees `p+a,q+b`. It does not use `b*(p+a)`.
- `associator_inverse` writes the reverse summand equation, using the ordinary
  module-sheaf associator inverse and the nested left inclusions.
- `symmetry_inverse` identifies `(β_ E F).inv` with `(β_ F E).hom`.
- `shift_natural`, `associator_natural`, `symmetry_natural` state the chain-map
  naturality squares for arbitrary morphisms in all two or three complex arguments.
  Naturality of inverses follows from these squares and their actual iso inverses.
- `shift_unique`, `associator_unique`, `symmetry_unique` quantify over arbitrary
  chain maps of the indicated source and target. A map satisfying the prescribed
  component-summand formula equals the canonical map. This is uniqueness, not a
  chosen alternative normalization. Inverses are then unique by the iso laws.
- `associativity` writes both full paths starting at
  `((E⟦a⟧) ⊗ (F⟦b⟧)) ⊗ (G⟦d⟧)` and ending at
  `(E ⊗ (F ⊗ G))⟦(a+b)+d⟧`. The left path shifts the target associator; the right
  path starts with the source associator. An `eqToIso` on `Int.add_assoc` identifies
  `a+(b+d)` with `(a+b)+d`. Here `d` is the node's integer `c`.
- `symmetry` writes `t_{a,b} ≫ σ[a+b]` equal to `(a*b).negOnePow` times
  `σ_{E[a],F[b]} ≫ t_{b,a}`, followed by the canonical `b+a=a+b` index identification.
- `associativity_coefficients` states equality of the exact signs with exponents
  `bp+d(p+q)` and `dq+(b+d)p`.
- `symmetry_coefficients` states equality of the exact signs with exponents
  `bp+(p+a)(q+b)` and `ab+pq+aq`.

The three formula predicates are equalities of module-sheaf morphisms on entire
component tensor summands, not statements merely about chosen global sections.
The existing sheaf-tensor universal property makes these equivalent to the node's
formulas on all local pure tensors. For triple tensors use it in each factor with
the product-preserving sheafification argument in the node's proof. The predicates
thus include every local section and impose no extra condition. Compatible-index
equality binders just select the same summands; their equalities always exist from
the displayed sums. No global generation assertion is used. This presentation also
avoids expensive repeated unfolding of the alternative generator bifunctor API.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and its
  cochain framework; shifts are the already defined
  `CochainComplex.shiftFunctor` in `HomotopyCategory.Shift`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  `mapBifunctorShift₁Iso`, `mapBifunctorShift₂Iso`, their full summand formulas,
  and the integer `CommShift₂Int` interface recorded by the shift dependency.
- `Sheaf.Algebra.Homology.RingedTensorComplexConstraints`:
  `CategoryTheory.RingedDerivedNative.complexConstraints`, with its existing
  `symmetryPure` and `associatorPure` formulas. This is a proof-dependency import;
  the present theorem also states uniqueness and shift coherence absent there.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` supplies the
  native sheaf tensor, symmetry, additivity and coproduct-preservation instances.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `WeilConjectures.coefficientTensorGenerator` and `coefficientTotalTensor`
  were read to check that the native tensor constraints are the same tensor. The final
  statement uses the recorded `HomologicalComplex.ιTensorObj` inclusions directly,
  so no second generator or total tensor is defined.
- Proof-only direct imports cover `LargeSetSheafification`,
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`,
  `TensorColimitsIndependentCoefficients`, and Mathlib's lifted commutative-group
  adjunction. Module sheafification and left exact set sheafification also occur
  through the imported framework. All stated proof dependencies are imported.

Source reading: `literature/stacks-project/sites-cohomology.tex`,
`lemma-symmetric-monoidal-cat-complexes` (Tag 0FPQ), and
`literature/stacks-project/more-algebra.tex`, `section-sign-rules`,
`item-shift-tensor`, `item-flip-tensor-product`. The node explicitly distinguishes
its shifted-degree normalization from a verbatim assertion of the Stacks text.
The complete nine-step proof from the node is carried into the theorem docstring.

Edge cases checked before writing: negative shifts and negative cochain degrees
are retained by `ℤ` and `Int.negOnePow`; the two exponent differences are zero
and `2bp`, respectively. Zero complexes, the zero ring and characteristic two
require no cancellation or nonzero hypothesis. Empty sites make the section
formulas vacuous, consistently with the zero module-sheaf category. The degree
fibres of ℤ² and ℤ³ are allowed countable coproducts even for unbounded complexes.
In particular the inverse normalization is checked using shifted first degree p.
There is no K-flatness, localization, or degree-zero-source premise.

Searches (performed before introducing helpers):

- `msearch.py ... leanfinder`, query: “For unbounded cochain complexes of sheaves
  of modules, total tensor integer shifts are coherent with associators and signed
  symmetry”. Eight hits included `mapBifunctorShift₂Iso` and the double-total
  shift interchange and inverse-summand formulas; none states this whole node.
- `msearch.py ... loogle`, query:
  `CochainComplex.mapBifunctorShift₁Iso, CochainComplex.mapBifunctorShift₂Iso`.
  One hit: `mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso`, the existing
  mixed extraction comparison, not the triple/symmetry theorem.
- `msearch.py ... grep`, query:
  `mapBifunctor.*(associator|braiding)|shift.*tensor.*(assoc|braid)` under
  `Algebra/Homology`. Six hits locate generic `mapBifunctorAssociator` machinery.
- `msearch.py ... leansearch`, query: “Total cochain tensor associator symmetry and
  integer shift comparison signed coherence”. Eight results concern ordinary shift
  and Hom-complex shift formulas; no exact statement.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib's homology directory
  found existing shift/associator compatibility in upstream `MonoidalShift.lean`,
  the Koszul braiding summand in upstream `Monoidal.lean`, and the project native
  pure-section constraint module. Their signatures/docstrings were read and reused.
  Search for the item's id in `lean/WeilConjectures` found no attached declaration.
  Search for `totalTensorShiftIso` / `totalTensor_signed_coherence` found no collision.

No new DAG nodes, dependency-record repairs, statement corrections or disputed
statements are needed. The node copy differs only in `lean`.

## Second reading by Q124

This is the dispatcher's required author check, not an independent review; no other
agent was started. I reread the node and the finished module clause by clause.
The generic predicates are definitions only; the theorem specializes them to the
exact ringed-site module category and has no extra monoidal or coproduct assumptions.
The original two maps in the first coherence display require explicit source and
target associators: both occur in `totalTensorCoherence_associativity`. Its equality
transport goes from `a+(b+d)` to `(a+b)+d`, in the required direction. In the second
identity the reverse extraction ends in shift `b+a`; the transport to `a+b` is explicit,
and the outer scalar is `(a*b).negOnePow`. All summand equations use shifted p in the shift
and inverse formulas; the symmetry afterwards uses unshifted `p+a,q+b`. Naturality,
uniqueness, the three inverse descriptions and both coefficient identities are
individual fields, not just mentioned in docstrings. The canonical maps have real
data and the theorem alone is postponed. No mathematical mismatch was found. The native module-sheaf associator and
braiding render the unsigned reassociation and pure-tensor swap within the summand
equations, as verified from the recorded constraint source.
Explicit universe arguments were added after an elaboration ambiguity; the logical
clauses were factored into predicates after the initial large structure exceeded
Lean's heartbeat budget. The source statement and all cases remain the same.

Elaboration repair: the final predicates use component-inclusion morphisms and
generic categorical parameters. At the theorem these parameters are all the native
module-sheaf instances. No time limit or heartbeat limit was raised.

Validation: prescribed `scompile.py` passed both the sandbox module (17.1 s) and
the final module name (16.0 s), with no errors or warnings. The dry run and delivery
recompile the final packet, including the copyright header added afterward.
