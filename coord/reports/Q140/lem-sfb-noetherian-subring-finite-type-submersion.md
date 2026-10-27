## Worker report

The module `Sheaf.RingTheory.NoetherianSubalgebraFiniteTypeSubmersion` states
`Subalgebra.finiteType_of_isNoetherianRing_of_universallySubmersive` with proof `sorry`.
There is one theorem and no new definition. The node is unchanged except for `lean`.

Source checked: Alper, arXiv:1005.2398v3, Theorem 6.2.1,
https://arxiv.org/html/1005.2398v3#S6.SS2 . Its hypotheses are Noetherian Y and S,
finite type X over S, and quasi-compact universally submersive X over Y. Here
S = Spec k, X = Spec E and Y = Spec R; affineness supplies quasi-compactness.
This agrees with the node's affine specialization. No statement correction is needed.

Hypothesis and conclusion correspondence:

- “k a field”: `(k : Type u) [Field k]`, using `Field` exactly as recorded by
  `def-weil-field`.
- “E a finitely generated commutative k-algebra”: `(E : Type v) [CommRing E]
  [Algebra k E] (hE : (algebraMap k E).FiniteType)`. `RingHom.FiniteType` is the
  recorded declaration of `def-weil-pbc-finite-type-algebra`; by definition it is
  `Algebra.FiniteType` for the induced algebra structure, equivalently finite algebra
  generation. This is not the stronger `Module.Finite` condition.
- “R ⊆ E a k-subalgebra”: `(R : Subalgebra k E)`. The underlying ring is the
  subtype R, its k-algebra is the inherited one, and its action on E is the canonical
  inclusion. No arbitrary map, injectivity hypothesis, or separate tower is supplied.
- “R Noetherian”: `[IsNoetherianRing R]`, the recorded notion, whose definition says
  all ideals are finitely generated.
- “for every commutative R-algebra L”: the hypothesis `hsub` binds
  `∀ (L : Type (max u v w)) [CommRing L] [Algebra R L]`. All universes are explicitly
  declared (`universe u v w`); `autoImplicit` is false. The test universe contains the
  universes of k and E; w permits enlargement. It cannot accidentally test only
  smaller rings. As usual algebra structures transport along equivalences/ULift.
- “continuous map Spec(E ⊗_R L) → Spec L”: it is exactly
  `AlgebraicGeometry.Spec.map (CommRingCat.ofHom
  (Algebra.TensorProduct.includeRight : L →ₐ[R] E ⊗[R] L).toRingHom)`.
  The map on rings sends l to 1 ⊗ l, with the R-algebra structure on E induced by
  the actual subalgebra inclusion. The scheme map coerces to its continuous map on
  underlying Zariski spaces. This uses the recorded `AlgebraicGeometry.Spec.map`.
- “surjective and a target subset is open iff its inverse image is open”:
  `Topology.IsQuotientMap` of that map. Its Mathlib docstring states these exact two
  clauses; it extends `IsCoinducing` and has field `surjective`. The openness iff is
  `Topology.isCoinducing_iff` (whose orientation is the symmetric equivalent).
- “R finitely generated as a k-algebra”: `(algebraMap k R).FiniteType`, again using
  the recorded `RingHom.FiniteType`, with R's inherited k-algebra.
- “No finiteness of E as an R-module is assumed”: the signature has no such
  hypothesis, no finite-dimensionality assumption, and no nontriviality restriction
  on E, R or L. This final sentence specifies the absence of an assumption, not
  an additional conclusion.

Statement dependency declarations read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs | Field |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Spec, AlgebraicGeometry.Spec.map |
| def-weil-pbc-finite-type-algebra | Mathlib.RingTheory.FiniteType | RingHom.FiniteType |

Their full definitions and source docstrings were inspected, including
`Algebra.FiniteType` and `isNoetherianRing_iff_ideal_fg`. Additional existing APIs are
`Subalgebra`, `Algebra.TensorProduct.includeRight`
(`Mathlib.RingTheory.TensorProduct.Basic`) and `Topology.IsQuotientMap`
(`Mathlib.Topology.Defs.Induced`, publicly available through `Mathlib.Topology.Maps.Basic`).
No notion needed an extra node or dependency repair.

All recorded proof-dependency modules are imported without `public`; Mathlib leaves
are imported from their recorded files. The one proof dependency without a declaration,
`lem-sfb-submersive-dense-open-closed-surjectivity`, has no module to import and is
explicitly named at step 3 in the proof docstring. It is not needed to type this
statement. The full ten-step accepted DAG proof is rendered in the theorem docstring:
auxiliary domain case; admissible flattening; integral blowup charts; horizontal
support surjectivity; source descent; finite-coefficient descent of charts and gluing;
projective coherent H0 finiteness; the injection of B into global sections; prime
quotients; and prime filtration. In particular the chosen flat open U is distinguished
from the possibly larger centre complement V, as in the reviewed DAG proof.

Edge cases checked before and after writing:

- E = 0 is allowed. Then R is the corresponding trivial subalgebra, spectra are empty,
  and the finite-generation conclusion is correct. No `[Nontrivial E]` is imposed.
- L = 0 is among the tests: both its spectrum and the tensor spectrum are empty,
  and the unique empty map is a quotient map. No nontriviality or flatness restriction
  on L occurs.
- R = E (when Noetherian) gives the identity after every base change and returns
  the assumed finite generation.
- E = k and R the scalar subalgebra is included. Zero algebra generators are allowed
  by `RingHom.FiniteType`; neither a positive number of generators nor positive
  transcendence degree is imposed.
- Nonreduced E, R and L, multiple irreducible components, and arbitrary field
  characteristic are allowed by the typeclasses. The proof plan explicitly uses
  prime filtration rather than assuming R reduced or a domain.
- E = k[X] and R = k show why no module-finiteness assumption belongs here:
  the map to Spec k is universally open and surjective, but k[X] is not a finite
  k-module. The statement includes this case.

Searches made on 2026-10-24:

1. `msearch.py ... leanfinder "A noetherian subalgebra of a finite type algebra over
   a field is finite type if its spectrum map is universally submersive"`: eight hits,
   including `Subalgebra.fg_of_noetherian`, Artin--Tate-style `fg_of_fg_of_fg`, and
   essential finite type. None proves this statement. `fg_of_noetherian` assumes
   Noetherianity as a module over the base, much stronger than ring Noetherianity.
2. `msearch.py ... loogle "Algebra.FiniteType, IsNoetherianRing, IsQuotientMap"`:
   no hits; service reported unknown unqualified identifier `IsQuotientMap`.
   The qualified declaration was then read directly in Mathlib.
3. `msearch.py ... grep "submersive|Submersive|fg_of_noetherian"`: 25 hits, on
   submersive presentations and unrelated Noetherian module algebra-generation lemmas.
4. `msearch.py ... leansearch "finite type descent noetherian subalgebra universally
   submersive spectrum"`: eight hits, including `RingHom.FiniteType`,
   `Subalgebra.fg_iff_finiteType`, and `Subalgebra.fg_of_noetherian`; no exact theorem.
5. Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
   `submersive|Submersive|noetherian.*[Ff]inite[Tt]ype|finiteType.*[Ss]ubring`:
   no matching theorem. The existing algebraic-space universal-submersivity predicate
   lives on algebraic-space presheaf maps, not the explicit affine tests of this node;
   its source `SpaceSubtrusive.lean` was read. No duplicate predicate is introduced.
6. Direct search for this item id in `lean/WeilConjectures`: no hits. Direct search of
   Mathlib and both project trees for
   `finiteType_of_noetherian_of|finiteType_of_universally|finiteType_of.*submers`:
   no declaration collision or exact existing theorem.
7. Searched existing tensor base-change maps in both project trees and inspected
   Mathlib `includeRight`, `Spec.map`, and `Topology.IsQuotientMap` definitions.

Validation: prescribed `scompile.py Q140 lem-sfb-noetherian-subring-finite-type-submersion
<module>` passed both sandbox and library module modes (9.9 s and 8.0 s), with no
reported errors or non-sorry warnings. All delivered Lean lines are at most 100
characters. No local Lean build, shared repository write, or direct Git command was used.

No STATEMENT-DISPUTED flag, new nodes, dependency repairs, or node faults.

## Second reading by Q140

A separate second pass through the node and completed source was performed in this
session. The dispatcher explicitly prohibits other agents, so this is a second reading
by the same worker rather than a claim of an independent worker review; the maintainer's
independent delivery review remains authoritative.

The field, finite-type ambient algebra, actual subalgebra, ring Noetherianity,
unrestricted commutative algebra base changes, quotient-map condition, and finite-type
conclusion each match the corresponding binders and expression listed above. In
particular `includeRight` has domain L and codomain E ⊗[R] L, so contravariance of
`Spec.map` gives the required direction. The canonical R-action on E comes from the
subalgebra, and the algebra structure in the conclusion comes from the same k-action.
The quotient-map structure includes surjectivity, not just reflection of open sets.
No finite-module, reducedness, domain, or characteristic hypothesis was introduced.
The maximum universe in the test type avoids a vacuous smaller-universe condition.
The ten-step proof docstring preserves the integral auxiliary argument without
incorrectly requiring R/p → E/pE to be injective. No mismatch or correction was found.
