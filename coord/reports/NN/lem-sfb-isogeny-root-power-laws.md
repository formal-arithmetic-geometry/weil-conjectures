## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.IsogenyRootPowerLaws` states
`AlgebraicGeometry.isogeny_root_power_laws`, with its sole proof `sorry`.
There are no new definitions, dependency replacements or statement corrections.
Only the item's `lean` field changes.

Sources read: Milne, Algebraic Groups (2017), printed pp.484--487, in particular
Definitions 23.1--23.2 and Proposition 23.5, formulas (144)--(147) and its final
kernel criterion. Formula (146) explicitly quantifies over every k-algebra.
The current blueprint unit `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was read; this is a supporting Milne theorem, not that unit's own statement.
The theorem docstring carries all eleven proof steps of the node with their
cited prerequisites. No proof is attempted.

Hypotheses and object identifications, checked against the complete node:

| Node hypothesis/notion | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| Affine finite type reductive groups A,D | Bundled `Grp (Over (Spec (.of F)))` and `hA`, `hD : ReductiveTorusCentralizer.IsReductive ...`. Its definition includes `SolvableGroupStructure.IsAlgebraic` (affine and finite type), smoothness, geometric connectedness and the triviality of every smooth connected normal unipotent closed subgroup after algebraic closure. Over algebraically closed F this is the node's condition. |
| Unipotence means a faithful geometric matrix realization | The reused `SolvableGroupStructure.IsUnipotent` inside `IsReductive` has a closed faithful GL representation and nilpotence of g-1 over every algebraically closed extension; no new predicate is introduced. |
| Closed split maximal tori | `iA`, `iD`, `hTA`, `hTD`, `hsplitA`, `hsplitD`. `IsMaximalTorus` includes the closed subgroup and torus conditions and maximality against larger tori. The existential split ranks allow rank zero. |
| Character and cocharacter lattices | The actual `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))` and the reverse Hom groups, exactly as in the recorded Borel-pair structure module. `IsCommMonObj` exposes their canonical pointwise commutative laws; these are the already available torus and Gm structures, not restrictions on the group. |
| Roots, coroots and integer dual pairing | `ΦA`, `ΦD`, `PA`, `PD : RootDatum ...`; `hrootA`, `hrootD` identify the embedded roots with those actual characters. `hpairA`, `hpairD` identify the perfect pairing with composition and the integer power map. `RootDatum` already contains the finite free lattice structures and perfectness. |
| Actual adjoint roots | `aA`, `aD` and `hconjA`, `hconjD` identify the actions with actual conjugation. `hweightsA`, `hweightsD` identify the finite root sets with exactly all nonzero character weights using `TorusCharacterTangent.weightSpace`; these are not differentials of characters. |
| Geometric coroots | `hcorootA`, `hcorootD` unpack the geometric reflection normalization of the recorded rank-one theorem: for each root its lattice reflection is induced by conjugation by an actual rational normalizer representative. The first equality is an equality of morphisms T→G, so implies normalization after every scalar extension. The second is the reflection formula for every character. This identifies PA/PD's coroots with the group's coroots. Merely supplying an abstract root datum with the right roots and composition pairing would leave possible central cocharacter components unconstrained. This is object identification, not a separability or centrality assumption on f. The rank-one dependency supplies these witnesses for every group in scope. |
| Root subgroups and any chosen parametrizations | `UA`, `UD`, `jA`, `jD`, `hUA`, `hUD` specify closed subgroups, normalization by T and equality of their tangent images to the corresponding character weight spaces. `uA`, `uD` are arbitrary group-scheme isomorphisms from the recorded Ga. They imply smoothness and connectedness, so those are not extra hypotheses. The root-subgroup uniqueness theorem identifies precisely these subgroups. |
| Faithfully flat homomorphism f with finite scheme kernel | `f : A ⟶ D`, `hff : f.hom.hom.left.appTop.hom.FaithfullyFlat`, `hfinite : IsFinite (GrpObj.ker f.hom.hom).hom`. The ring-map predicate is faithful flatness of the coordinate-algebra map; finiteness over Spec F is finite-dimensional coordinate algebra. |
| f(TA) lies in TD, restriction fT | `fT : TA ⟶ TD` and `hfT : fT ≫ iD = iA ≫ f`. Because iD is a closed inclusion the factorization is unique; this supplies the specified restriction, not an arbitrary map. |

Each conclusion:

| Node conclusion | Lean rendering |
| --- | --- |
| fT faithfully flat and finite kernel | First two conjuncts, using `FaithfullyFlat` and `IsFinite (GrpObj.ker fT.hom.hom).hom`. |
| f* is injective | `Function.Injective (fun χ ↦ fT ≫ χ)` on actual group-scheme characters. |
| Finite cokernel of f* | `Finite` of the actual additive character lattice quotient by `Submodule.span ℤ (Set.range (fun χ ↦ Additive.ofMul (fT ≫ χ.toMul)))`. Composition is additive, so its image already is a subgroup/ℤ-submodule, and this span is exactly the image. This is finiteness of the cokernel, not just rank equality. |
| Bijection alpha↔beta | `b : ΦA ≃ ΦD` in the stated direction. |
| Characteristic powers e_alpha | `q : ΦA → ℕ` with `∀ α, ∃ m : ℕ, q α = ringExpChar F ^ m`. Mathlib's `ringExpChar` is max(ringChar F,1), hence 1 in characteristic zero and p in characteristic p. The case m=0 is included. |
| Nonzero constants | `c : ΦA → Fˣ`, chosen after the arbitrary input parametrizations. |
| f* beta = e_alpha alpha | `Additive.ofMul (fT ≫ (PD.root (b α)).toMul) = q α • PA.root α`. |
| f_* alpha^vee = e_alpha beta^vee | `Additive.ofMul ((PA.coroot α).toMul ≫ fT) = q α • PD.coroot (b α)`. Both directions are actual compositions, with the same q. |
| Parameter law for every commutative F-algebra and every a | The `∀ (α) (R : Type u) [CommRing R] [Algebra F R] (x : R)` conjunct uses the already recorded `TorusCharacterTangent.additiveParameterPoint F x`, postcomposition by uA,jA,f, and on the right the point with coordinate `algebraMap F R (c α : F) * x ^ q α`, followed by uD,jD. No reducedness, field, nontriviality or characteristic hypothesis is put on R. |
| Scheme-theoretic f(U_alpha)=U_beta | `∀ α, ∃ g : UA α ⟶ UD (b α), g ≫ jD (b α) = jA α ≫ f ∧ g...appTop.hom.FaithfullyFlat`. A faithfully flat map onto a closed subgroup gives precisely that scheme-theoretic image. This does not assert the generally false surjectivity on every test algebra's points. |
| Full kernel central iff every e_alpha=1 | The final iff quantifies over every commutative F-algebra R, all kernel R-points x and all A(R)-points g, and asserts commutation after the canonical `GrpObj.kerι`. The other side is `∀ α : ΦA, q α = 1`. Quantification includes every scalar extension and infinitesimal points; it is not a condition on F-points alone. |

Dependency declarations read and reused:

- `Field` in Mathlib.Algebra.Field.Defs; `IsAlgClosed` in
  Mathlib.FieldTheory.IsAlgClosed.Basic (the algebraically closed part of the
  algebraic-closure dependency, with no extraneous choice of closure).
- `CategoryTheory.GrpObj`, `Grp` in Mathlib.CategoryTheory.Monoidal.Grp;
  `GrpObj.ker`, `kerι` and `IsSubgroupScheme`, `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme` in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `AlgebraicGeometry.Smooth` in Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  `ConnectedSpace` in Mathlib.Topology.Connected.Basic,
  `LocallyOfFiniteType` and `QuasiCompact` in the recorded Mathlib morphism modules.
- `StandardGroupSchemes.affine`, `map`, `multiplicative`, `additive` and their
  actual group structures in Sheaf.AlgebraicGeometry.StandardGroupSchemes.
- `AlgebraicGeometry.reductive_borel_pair_structure` in
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure;
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus` and
  `TorusCharacterTangent.weightSpace`, `IsStable` in its public dependency modules.
- `TorusCharacterTangent.reductive_root_subgroup_parametrizations` and
  `additiveParameterPoint` in
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations.
  Their full signatures and docstrings were read, not just their names.

The already stated proof dependencies are imported privately: character antiduality,
homomorphism factorization, additive subgroup polynomial quotient, rank-one reflections,
smooth orbit geometry, Bruhat charts, Borel root product coordinates, dense-open dimension
comparison, polynomial Krull dimension and torus self-centralizer, in the modules named
in the source imports. The three proof dependencies with no current Lean attachment
(`lem-sfb-quotient-borel-torus-images`, `lem-sfb-split-torus-hom-matrices`,
`lem-sfb-reductive-centre-root-quotient`) are named in the proof docstring and not imported;
no statement object needed here is missing. No import cycle was encountered.

Searches (all three remote search kinds plus LeanSearch were actually executed through
msearch.py with this group/item):

- LeanFinder: "An isogeny of reductive algebraic groups maps root subgroups by characteristic
  powers and induces dual character and cocharacter lattice maps". Eight hits were abstract
  RootPairing Hom/Equiv/map results, none an algebraic-group power-law theorem.
- Loogle: "RootPairing.Hom, ExpChar, Module.FaithfullyFlat". Zero hits.
- Mathlib grep: "isogeny|Isogeny|root.*power". Twenty-five displayed hits were cyclotomic,
  primitive-root or unrelated power-basis statements, none this theorem.
- LeanSearch: "An isogeny of split reductive group schemes induces a bijection of roots and
  root subgroup power maps". Eight hits concerned root-pairing reflections/equivalences,
  Galois root sets and primitive roots; none matches this group-scheme statement.
- Project rg searches of WeilConjectures and Sheaf for isogeny/Isogeny, root power and
  the node id found the general `IsIsogeny` definition and other isogeny results,
  including CentralIsogenyBorelRootCompatibility, which explicitly cites this node
  in its proof and only treats central maps. No existing theorem gives this statement.
  `dag/lean_names_upstream.json` likewise records only the existing abelian-variety
  isogeny notions/results. Searches for the proposed name found no collision.

Edge cases checked before writing and rechecked against the signature:

- Pure tori and the trivial group: root sets may be empty; b is the empty equivalence,
  root laws are vacuous, the character isogeny remains asserted and the centrality
  equivalence correctly says any such torus kernel is central. No roots-span assumption.
- Characteristic zero: ringExpChar=1 makes every q=1. No prime or separability binder
  excludes this case.
- Frobenius in positive characteristic: q=p^r is allowed; the parameter law is valid
  over nonreduced algebras, and the full kernel can be noncentral even when F-points
  of a root kernel see only the identity. No differential injectivity is assumed.
- Central inseparable SL_p→PGL_p: q=1 on roots is compatible with a nonreduced torus
  kernel and a character cokernel with p-torsion. No prime-to-p condition is imposed.
- Characteristic two rank one: actual characters and integral composition pairing
  preserve the weight/coroot information that differentiated characters could lose.
- The zero test algebra and a=0 are included. Units in F map to units in any test
  algebra, and the usual zero-ring interpretation of its unique point causes no issue.
- Arbitrary prescribed root parametrizations: uA,uD are universally bound before c
  is chosen, so c may change with them, as required.
- All schemes, coefficient algebras and test algebras use the dependencies' explicit
  common universe u; there is no independent smaller test-algebra universe and no
  equality imposed between independently specified universes.

Validation: the delivered module compiled cleanly via scompile.py in both sandbox
and library module modes. All variables/universes are explicitly bound, with
`set_option autoImplicit false`. All lines are at most 100 characters. The single
postponed named theorem has its complete proof plan and matching DAG node.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
