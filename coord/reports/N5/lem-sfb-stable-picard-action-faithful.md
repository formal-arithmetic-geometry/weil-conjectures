## Worker report

The module `Sheaf.AlgebraicGeometry.StablePicardActionFaithful` states
`AlgebraicGeometry.stablePicardActionFaithful`, with `sorry` as its only proof.
It states the kernel-triviality formulation of faithful pullback action on the full
ordinary group of multidegree-zero invertible-sheaf classes. There are no new
definitions, helper axioms, dependency repairs, or statement corrections. The node
copy changes `lean` and adds the four statement dependencies required by the return.

Source checked: Deligne--Mumford, *The irreducibility of the space of curves of given
genus*, Theorem 1.13, printed p.85, and Lemmas 1.14--1.17 and the graph argument,
printed pp.85--87. Read the primary PDF at
https://www.numdam.org/item/PMIHES_1969__36__75_0.pdf . The theorem explicitly treats
the ordinary Picard-zero group of componentwise degree-zero invertible sheaves.
The docstring follows the seven proof steps of the node, including its existing
polarized-Jacobian replacement for the high-genus smooth input.

Hypothesis and clause matching:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`. These are
  Mathlib's recorded field and algebraic-closure notions. No characteristic is fixed.
- Genus at least two: `(g : ℕ)` and
  `(C : StablePointedModuli (Spec (.of k)) g 0)`. The structure's
  `genus_at_least_two : 2 ≤ g` supplies this bound, without a duplicate hypothesis.
  Its `genus` field uses the degree-one Zariski cohomology dimension on each
  geometric fibre, exactly as the recorded moduli definition prescribes.
- A curve over k itself: `_hbase : C.base = Over.mk (𝟙 (Spec (.of k)))` selects
  the fibre over the field point from the total family category. This is the
  presentation of the base, rather than a geometric extra assumption: any
  stable genus-g curve over k has precisely such a family presentation. The
  structure morphism used throughout is `C.projection ≫ C.base.hom`.
- Unpointed: the final parameter `0` of `StablePointedModuli` gives no sections.
  Stability is the structure's `stable` field using `IsStablePointedCurve`;
  this includes projectivity, flat finite presentation, connected nonempty
  reduced nodal geometric fibres of pure dimension one, and component stability.
  There is no smoothness or irreducibility hypothesis on the curve.
- Invertible sheaves modulo isomorphism: `L : C.curve.Pic` uses the existing
  `Scheme.Pic`, the invertible classes in the skeleton of the module category.
  Its existing commutative group operation is tensor product; this theorem needs
  only its underlying type and pullback map, not another group presentation.
- Degree zero on EACH irreducible component: `∀ Z : irreducibleComponents C.curve`.
  `C.curve.normalizedComponentMap Z` is the canonical map from the normalization
  of the reduced induced component, not a chosen auxiliary curve or arbitrary map.
  The expression
  `(C.curve.normalizedComponentMap Z ≫ C.projection ≫ C.base.hom).picDegree
    (Scheme.Pic.map (C.curve.normalizedComponentMap Z) L) = 0`
  computes the existing Picard degree after exactly the pullback required by the
  node. The field structure on the normalization is the displayed composite.
  Quantifying this condition inline avoids a second definition of Picard zero.
- A k-automorphism: `(a : C.curve ≅ C.curve)` and `_ha` saying its homomorphism
  commutes with that structure map. No order hypothesis is present.
- Triviality on all Picard-zero classes: `_hpic` quantifies every Picard class
  satisfying all of the preceding normalized-component degree equalities and
  asserts `Scheme.Pic.map a.hom L = L`. This is pullback, not an arbitrary action,
  and is equality of isomorphism classes, not equality of chosen sheaves.
- Conclusion: `a = Iso.refl C.curve`, equality of scheme isomorphisms, is exactly
  identity of the automorphism. No conclusion is restricted to underlying points.

Dependencies and declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`;
  also read the recorded `AlgebraicClosure` construction and its docstring.
- `def-sfb-stable-pointed-moduli-groupoids`:
  `AlgebraicGeometry.StablePointedModuli`,
  `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`; read all structure fields
  and the unpointed, genus and base conventions. Its stable predicate and canonical
  normalized component map are read from `Sheaf.AlgebraicGeometry.StablePointedCurve`.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`. Its existing scheme
  Picard class construction is `AlgebraicGeometry.Scheme.Pic` and pullback is
  `AlgebraicGeometry.Scheme.Pic.map` in
  `WeilConjectures.AlgebraicGeometry.PicardFunctor`, publicly supplied by `Curve`.
- Degree: `AlgebraicGeometry.Scheme.Hom.picDegree`,
  `WeilConjectures.AlgebraicGeometry.Curve`, computes
  `AlgebraicGeometry.Scheme.Modules.degree` of a representative with the displayed
  structural map. Read its full definition and docstring and the latter definition
  in `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`.
- `def-sc-picard-group`: `AlgebraicGeometry.Scheme.Pic` in
  `WeilConjectures.AlgebraicGeometry.PicardFunctor`, now an explicit public import.
- `def-sc-pic0`: `Scheme.Hom.picDegree` in
  `WeilConjectures.AlgebraicGeometry.Curve`. The scalar degree is applied separately
  to each normalized component; the total-curve `picZero` predicate is not used.
- `def-sfb-stable-pointed-curve`: `Scheme.normalizedComponentMap` in
  `Sheaf.AlgebraicGeometry.StablePointedCurve`, now a public statement import.
- `lem-pc-pic-presheaf-functorial`: the recorded definitional declaration
  `AlgebraicGeometry.Scheme.Pic.map` in
  `WeilConjectures.AlgebraicGeometry.PicardFunctor`. See the return repair below
  for the theorem-statement-dependency justification.
- Already stated proof dependencies are imported without `public`:
  `Sheaf.Combinatorics.FiniteGraphHomologyRigidity`
  (`finiteGraphHomologyRigidity`), and
  `WeilConjectures.AlgebraicGeometry.DensePoints`
  (`AlgebraicGeometry.Scheme.Hom.denseRange_fieldPoints`). The other proof nodes
  have no recorded Lean module at the time of reading, so have no import yet.

Edge cases checked before writing: empty markings are intentional (`Fin 0`).
The empty curve is excluded by the existing connected nonempty geometric fibre
condition, not by a new assumption. Genus zero and one for the TOTAL curve are
excluded by `genus_at_least_two`; normalized components of genus zero and one are
allowed and remain covered. Reducible curves, multiple intersection nodes and
self-nodes are allowed; all reduced normalized components are quantified. Thus
opposite nonzero component degrees with total degree zero do not meet `_hpic`'s
antecedent. The trivial class has zero degree on every component. All positive
characteristics, including two, and automorphisms of arbitrary order remain in
scope. The field, scheme and normalization live in the same explicitly declared
universe `u`, as prescribed by the dependency; their Picard classes live in `u+1`.
`autoImplicit` and `relaxedAutoImplicit` are both disabled.

Searches before writing (all through the required wrappers or read-only `rg`):

- `msearch.py ... leanfinder "Stable curve automorphism acting trivially on degree
  zero invertible sheaves is identity"`: eight hits about Weierstrass curves and
  Galois categories, no matching theorem.
- `msearch.py ... loogle "FaithfulSMul, PicardGroup"`: zero hits, unknown identifier
  `PicardGroup`; the correct scheme interface was subsequently found by `rg`.
- `msearch.py ... grep '([Pp]icard.*[Ff]aithful|[Ss]table.*[Cc]urve)'
  AlgebraicGeometry`: zero hits in Mathlib.
- `msearch.py ... leansearch "stable curve automorphism acts faithfully on Picard
  group degree zero"`: eight hits about actions of linear, ring and group
  automorphisms and ring Picard pullback; none about stable curves.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for Picard/degree declarations
  located `Scheme.Pic`, `Scheme.Pic.map`, `Scheme.Hom.picDegree`, and
  `Scheme.Modules.degree`. Read their definitions and docstrings. Searches for
  `multidegree|multiDegree|Multidegree|MultiDegree` found only unrelated symmetric
  product material. `Pic.*[Ff]aithful|picard.*[Ff]aithful|[Ss]table.*[Pp]icard`
  found only consumer proof prose. The item-id search in `lean/WeilConjectures`
  found no declaration of this theorem. The proposed theorem name was also
  searched in both Lean trees and `dag/lean_names_upstream.json`, with no match.

Validation: `scompile.py N5 lem-sfb-stable-picard-action-faithful` compiled the
module on the server in both sandbox and library contexts, cleanly. Every
postponed proof is the single named theorem with this DAG node and the complete
natural-language proof in its docstring. No STATEMENT-DISPUTED issue was found.

## Second reading by N5

This is the worker's own second pass, not an independent worker review; the
assignment requires delivery by this worker and the maintainer's independent
reading. No other agent was started. I reread the node alongside the final Lean
signature: the moduli bound supplies g ≥ 2; equality of the base object selects
Spec k; zero markings supplies unpointedness; each reduced normalized component
has its own zero-degree test; the automorphism is over k; all qualifying classes
are fixed; and the conclusion is identity as an isomorphism. In particular the
existing total-degree `picZero` predicate was deliberately not used for a
reducible curve, since it would impose a different condition. There were no
signature mismatches on this pass and no statement edits.


## Repair of return on immutable head 9c751c69b8a5

H2 is repaired by adding `def-sc-picard-group`, `def-sc-pic0`,
`def-sfb-stable-pointed-curve`, and `lem-pc-pic-presheaf-functorial` to the item's
`stmt_deps`. These are existing recorded nodes; no new node or dependency record
is introduced. The current main node still has the four original statement
dependencies and no Lean record. Comparison of that node with the retained
returned sandbox found only the delivered `lean` field different before this
repair. The wrapper will build the repair on current main. The theorem signature,
natural-language statement, proof plan, and proof dependencies stay verbatim.

The theorem-stmt_dep finding for `lem-pc-pic-presheaf-functorial` is intentional:
its recorded `lean.declarations` includes `AlgebraicGeometry.Scheme.Pic.map`,
which is a **definition**, not a theorem being assumed to prove this statement.
Its full definition in `PicardFunctor.lean` is pullback on the skeleton of modules
with the existing invertibility proof. The present signature needs precisely
this canonical map both on component normalizations and on the automorphism.
This dependency supplies an object occurring IN the signature; moving it to
`proof_deps` would again omit that object's recorded owner. No assertion of
functoriality is an additional hypothesis, and no theorem's conclusion is used
as a substitute for a definition. This is exactly the second option authorized
by the maintainer's return. The definition node `def-pc-picard-presheaf` owns
`picardPresheaf`, whose `map` is built from `Pic.map`, but rewriting the signature
to presheaf maps would require fibre-product identifications and would violate
the request to keep the signature. We therefore cite the existing node that
explicitly records `Pic.map`.

Import visibility now matches the added statement edges: `StablePointedCurve`
is a public import and `PicardFunctor` is explicitly publicly imported.
The advisory concerning `FiniteGraphHomologyRigidity` and `DensePoints` was
checked: both are existing `proof_deps` and are required as plain proof imports
by stages/2-statements.md section 3 rule 7. They remain plain imports to retain
the specified proof plan; neither contributes a hypothesis to the signature.

The second pass for this repair checked all four added IDs against their current
node records and read the full `Scheme.Pic`, `Scheme.Hom.picDegree`,
`Scheme.normalizedComponentMap`, and `Scheme.Pic.map` declarations. The
mathematics accepted by the maintainer is unchanged. This is the worker's own
check, with independent review left to the maintainer as in the dispatched brief.

Repair validation: the prescribed `scompile.py` completed successfully for the repaired
module in sandbox and library contexts, with no errors or warnings reported.
