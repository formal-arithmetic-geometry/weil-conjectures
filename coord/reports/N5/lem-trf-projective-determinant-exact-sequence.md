## Worker report

The delivery states all clauses of `lem-trf-projective-determinant-exact-sequence` in
`Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence`. It adds the missing determinant
construction in `Sheaf.LinearAlgebra.ProjectiveDeterminantModule`, with the new definition
node `def-trf-projective-determinant-module`. Every theorem has exactly `sorry` as its proof.
No statement correction or disputed statement is needed.

Source read: `literature/stacks-project/more-algebra.tex`, section Determinants, lines
36228–36349: the determinant definition, `remark-determinant-as-socle`, and both proofs
of `lemma-det-ses` (Tag 0FJB). The source explicitly identifies the determinant with the
annihilator of module vectors in its exterior algebra. This supplies an actual construction
for arbitrary varying local ranks, without choosing data from an unproved existence lemma.
The item still means its original glued determinant: the delivered local-identification
and localization statements identify this socle model with exactly those local top wedges
and transition maps, by the identity of their inclusions in the exterior algebra.

Hypothesis and clause correspondence:

- A commutative ring is `{R : Type u} [CommRing R]`. The three module carriers have separate
  universes `v,w,z`, `AddCommGroup` and `Module R` instances. There is no nonzero-ring,
  domain, local-ring, characteristic, or constant-global-rank assumption.
- The sequence maps are `i : U →ₗ[R] V`, `p : V →ₗ[R] W`. Its three exactness conditions are
  `hi : Function.Injective i`, `hp : Function.Surjective p`, and `hex : Function.Exact i p`.
  `Function.Exact` says precisely `p v = 0 ↔ ∃ u, i u = v`.
- Direct summands of finite free modules are expressed as `[Module.Finite R U]` and
  `[Module.Projective R U]`, and the corresponding two instances for V and W. This is
  the same finite-projective encoding used by the recorded standard-free-cover theorem.
- The determinant's real data is `Module.determinantModule R E`, the intersection over
  `m : E` of the kernels of right multiplication by `ExteriorAlgebra.ι R m`.
  This is the source's exterior-algebra socle, not an assumed invertible module or an
  arbitrarily chosen line. No data is postponed.
- `determinantModule_topExterior` gives the unique equivalence to `⋀[R]^n E` on every
  finite free chart, characterized by `(e x).val = x.val`. It is independent of which
  basis witnesses that rank. `determinantModule_localization` gives the unique localized
  determinant map q with `(q x).val = ExteriorAlgebra.scalarExtensionMap f x.val`, and
  asserts `IsLocalizedModule S q`. Applying these two theorems successively identifies
  the localized global determinant with exactly the chart's top exterior power.
  On overlaps the map is induced by the identity on the localized module, so these are
  precisely the top-exterior change-of-basis transition maps. The proof docstrings spell
  out their cocycle and refinement compatibility. Thus the globally constructed socle
  realizes the specified glued determinant, including when ranks vary among components.
- `determinantModule_finite_projective` asserts `Module.Finite` and `Module.Projective`
  for the determinant, and gives a finite standard cover generating the unit ideal with
  each localized determinant linearly equivalent to `Localization.Away (f j)` itself.
  This last equivalence specifies rank one, rather than mere local freeness.
- `determinantModule_zero` treats every `[Subsingleton E]` and gives the unique equivalence
  `determinantModule R E ≃ₗ[R] R` whose inverse is `algebraMap R (ExteriorAlgebra R E)`.
  This is the canonical meaning of `det(0)=R`, including its generator 1.
- The main theorem, `existsUnique_determinantExactSequence`, gives a unique R-linear
  equivalence from `determinantModule R U ⊗[R] determinantModule R W` to
  `determinantModule R V`. `IsDeterminantExactSequenceMap i p e` characterizes it by the
  source's second construction: for x,y and *every* exterior lift t with
  `ExteriorAlgebra.map p t = y.val`, its value has inclusion `ExteriorAlgebra.map i x.val * t`.
  Surjectivity of p supplies such lifts, and pure tensors span, so this genuinely
  characterizes the whole map. There is no arbitrary comparison isomorphism assumption.
- `determinantExactSequence_wedge` is the first construction's formula. It quantifies over
  every rank witness `_bU : Module.Basis (Fin r) R U`, `_bW : Module.Basis (Fin s) R W`,
  tuples u,w, and lifts t with `∀ j, p (t j) = w j`. Inputs x,y have exactly the pure-wedge
  inclusions in `hx` and `hy`; they exist uniquely by `determinantModule_topExterior`.
  The output is `ExteriorAlgebra.ιMulti R (r+s) (Fin.append (fun j ↦ i (u j)) t)`.
  The basis case is the displayed node formula; the arbitrary-tuple formulation is
  explicitly justified in the node's proof steps 4–6. Quantification over every t and
  every basis expresses independence of lifts and bases. No selected splitting appears.
- `determinantExactSequence_localization` is the localization square on pure tensors:
  `qV (e (x ⊗ₜ[R] y)) = e' (qU x ⊗ₜ[A] qW y)` for every submonoid S, localization A,
  and localized module models fU,fV,fW. The localized maps i',p' commute with the original
  maps on images of the localization maps. Both determinant isomorphisms satisfy their
  defining formulas, and the three q maps satisfy exactly the canonical exterior
  inclusion formulas. Their existence and uniqueness are the other delivered clauses;
  these hypotheses specify the canonical maps rather than arbitrary replacements.
  The localization formula is deliberately valid even without redundant finite-projective
  hypotheses once the characterized isomorphisms are supplied. In the item's setting
  those maps exist by the main theorem over each localized ring. Pure tensors span and
  tensor localization has its universal property, so this is the full localization
  compatibility square. Applying it after any further localization includes refinements.

Dependency declarations used:

- `Mathlib.Algebra.Module.Projective`: `Module.Projective`, with the split/lifting
  interpretations `Module.Projective.iff_split` and `Module.projective_lifting_property`.
- `WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover`:
  `Module.exists_standardFreeCover_of_finite_projective`. The recorded module is absent
  in the older source checkout; its current full source and proof docstring were read
  with `scompile.py --source`. Its signature uses the same finite/projective instances.
- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `ExteriorAlgebra`, `ExteriorAlgebra.ι`,
  `ExteriorAlgebra.exteriorPower`, `ExteriorAlgebra.ιMulti`, `ExteriorAlgebra.lift`,
  `ExteriorAlgebra.map`, `ExteriorAlgebra.ι_sq_zero`.
- `Mathlib.LinearAlgebra.ExteriorPower.Basic`: `exteriorPower`, with its canonical
  inclusion into `ExteriorAlgebra` and pure-wedge construction. The recorded exterior
  algebra node's declaration list names both the algebra and its homogeneous powers.
- `Mathlib.LinearAlgebra.TensorProduct.Basic`: `TensorProduct` and its pure tensors.
  The dependency is a Mathlib leaf and has no Lean record; its `mathlib_match` was read.
- `Sheaf.LinearAlgebra.ProjectiveDeterminantModule`: `Module.determinantModule` and
  `ExteriorAlgebra.scalarExtensionMap`, the new definition node in this delivery.

Recorded proof dependencies with statements are imported without `public`: the exterior
basis theorem, generic exterior localization, affine tilde/Gamma, module-sheaf gluing,
coherence, the standard-cover finite-projectivity criterion, top-exterior direct-sum,
tensor localization, and standard-cover exactness. Every delivered theorem has its source,
blueprint id, and a complete natural-language proof in its docstring.

Edge cases checked mathematically: U=0, W=0, both zero, a nontrivial ring with disconnected
spectrum and different ranks on its components, zero/empty standard opens, empty bases,
and R=0. Empty wedges are 1 and the (0,0) map is multiplication. Empty covers are possible
only over the zero ring and the unit-ideal criterion allows them. No factorial division
or antisymmetry-to-alternation inference is used, so characteristic two is included.
Separate carrier and coefficient universes are explicit, including for localized models.

Searches made (all before adding the definitions):

- `msearch.py ... leanfinder "determinant module finite projective locally constant rank
  top exterior power exact sequence"`: 8 scalar-determinant hits, including
  `LinearMap.det_eq_det_mul_det`; no varying-rank determinant module or line isomorphism.
- `msearch.py ... leansearch "determinant module of finite projective module annihilator
  in exterior algebra"`: 8 hits, headed by `LinearMap.det`,
  `LinearMap.associated_det_comp_equiv`, `Submodule.annihilator_top`; none defines this socle.
- `msearch.py ... leanfinder "socle of exterior algebra determinant line finite projective
  module"`: 8 hits per run; exterior powers, scalar determinants and their consequences,
  not the socle determinant or this exact-sequence theorem.
- `msearch.py ... loogle "ExteriorAlgebra.map, LinearEquiv"`: zero hits.
- `msearch.py ... grep "determinantModule|determinant.*[Ss]ocle|det.*[Ee]xact"
  LinearAlgebra`: only `Matrix/Gershgorin.lean`, an unrelated scalar determinant proof.
- `msearch.py ... grep "determinantModule|annihilator.*Exterior|socle"
  LinearAlgebra/ExteriorAlgebra`: zero hits.
- `rg` for determinant module/line terminology in `lean/Sheaf` and the upstream
  `WeilConjectures` sources finds other determinant constructions (Koszul and
  constant-rank sheaf/representation determinants), not this finite-projective socle.
  `rg` for `determinantModule|IsDeterminantExactSequenceMap|scalarExtensionMap` in both
  project source trees and Mathlib's LinearAlgebra gives no hits. The item's blueprint id
  has no hit in upstream `WeilConjectures`.
- DAG grep and `tools/blueprint_refs.py search determinant` find no existing socle-module
  definition node. The 47 blueprint hits include the constant-rank sheaf theorem
  `lem-sc-determinant-short-exact` and representation determinant `def-mg-determinant-line`;
  both nodes were read and concern different objects. `blueprint_refs.py ancestor` returns
  `lem-trf-local-term-locality`, which is recorded for the new node.

Validation: both delivered modules compiled separately in dependency order with
`scompile.py N5 lem-trf-projective-determinant-exact-sequence <both files>`; all sandbox
and library passes were clean, with no warnings. The source-file passes took under
three seconds each. No global build or direct live-library write was run.

## New nodes

`def-trf-projective-determinant-module` defines the determinant as the exterior-algebra
socle (intersection of actual linear-map kernels), together with the canonical exterior
map under coefficient extension. Its source is the explicit socle remark immediately
before Tag 0FJB, which is also the model used in Tag 0FJB's second proof. The searches
listed above, and preserved as tool results in the node's `mathlib_searches`, find neither
an existing DAG definition nor an existing project/Mathlib declaration of this varying-rank
module. The new definition is cited from the item, with the item's original statement
and all other original fields retained. It uses the recorded exterior-algebra definition
and the recorded projective-module notion. Its data contains no `sorry`.

## Second reading by N5

Author self-check, with the node, source and both Lean files open; the dispatcher explicitly
prohibits starting other agents. The maintainer's independent delivery review remains the
independent reading. This section does not claim that a second worker was run.

I checked the commutative-ring binder, the six finite/projective instances, all three
exactness hypotheses, the direction and order of the determinant tensor factors, and the
inclusion formula characterizing the canonical map against the node. I then checked
invertibility has rank one rather than only local freeness; normalization covers all zero
modules; top wedges agree by their actual inclusions; and localization maps are constrained
by their actual exterior-algebra maps. The wedge theorem includes arbitrary lifts and
all bases with `Fin r` and `Fin s`, including zero. The localization theorem covers all
submonoids and all compatible localized models, with explicit independent universes.
The source's socle remark justifies the chosen concrete model of the glued determinant.
No mismatch or silent statement change was found; no dependency record was replaced.
