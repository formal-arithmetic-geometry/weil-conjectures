## Worker report

The delivery states `AlgebraicGeometry.exists_normal_proper_completion_divisorial_boundary`
in `Sheaf.AlgebraicGeometry.NormalDivisorialCompletion`. Its only proof is `sorry`.
There are no definitions, helper theorems, new nodes, dependency modules, or statement
corrections. The theorem docstring reproduces all ten reviewed DAG proof steps.

The source was checked in Milne, Algebraic Groups (2017), printed p.154 (PDF p.166),
which refers to the rational-action proof, and in Milne (2013), Proposition 4.1,
first paragraph of its proof, and Aside 5.4:
https://arxiv.org/html/1311.6060v2 . The latter gives the completion, boundary blowup,
and normalization route, with Nagata permitted instead of quasi-projectivity. The
reviewed node supplies the detailed general-scheme proof, without requiring a group
structure on Y. The Lean statement retains this generality.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` |
| Y a k-scheme | `Y : Scheme.{u}` and the explicit structure map `f : Y ⟶ Spec (.of k)` |
| Separated over k, diagonal a closed immersion | `[IsSeparated f]`, with field `isClosedImmersion_diagonal` |
| Finite type over k | `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded finite-type interface |
| Smooth over k | `[Smooth f]` |
| Connected and nonempty | `[ConnectedSpace Y]`; its `toNonempty` field includes the explicitly stated nonemptiness, so no independent redundant assumption is needed |
| Not proper over k | `hnotproper : ¬ IsProper f` |
| Y is integral | `IsIntegral Y`, the first conclusion conjunct |
| Existence of a k-scheme X0 | `∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) ...` |
| X0 normal and integral | `IsNormalScheme X`; this recorded predicate is `IsIntegral X ∧ ∀ x, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)` |
| X0 proper over k | `IsProper p`; this already includes separatedness, local finite type, and universal closedness, with quasi-compactness following from universal closedness |
| Open immersion j0 over k | `j : Y ⟶ X`, the existential instance `(_ : IsOpenImmersion j)`, and `j ≫ p = f` |
| Dense image | `DenseRange j.base` |
| The reduced complement E0 | `(Scheme.IdealSheafData.vanishingIdeal ⟨(j.opensRange : Set X)ᶜ, j.opensRange.isOpen.isClosed_compl⟩).subscheme` |
| E0 nonempty | `Nonempty` of this exact subscheme |
| Dimensions are topological Krull dimensions | `topologicalKrullDim`, valued in `WithBot ℕ∞` |
| dim X0 = dim Y a positive finite integer | `∃ d : ℕ, 0 < d ∧ topologicalKrullDim Y = (d : WithBot ℕ∞) ∧ topologicalKrullDim X = (d : WithBot ℕ∞) ∧ ...` |
| Every irreducible component of E0 has dimension dim Y - 1 | `∀ C ∈ irreducibleComponents` of that exact reduced subscheme, `topologicalKrullDim C = ((d - 1 : ℕ) : WithBot ℕ∞)`; C has its subspace topology, and `0 < d` ensures natural subtraction is the stated integer subtraction |

The complement is the actual canonical quotient scheme, not a chosen scheme or a
hypothesis about an unspecified boundary. Mathlib's `vanishingIdeal` docstring identifies
its quotient with the reduced induced structure. The upstream instance
`Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal` proves reducedness, and
`range_subschemeι` with `coe_support_vanishingIdeal` identifies its support with the
closed complement. Thus no extra reducedness conjunct is needed to specify the object.
The closed boundary also inherits separatedness and finite type from the proper X.

### Dependency declarations used

Read every original stmt_dep's statement, recorded Lean or Mathlib match, declaration
signature and docstring in the pinned sources:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-algebraic-closure`: the algebraically-closed clause `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic; also inspected its recorded `AlgebraicClosure`
  in Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure and `IsAlgClosure` in Basic.
  No algebraic closure is chosen, since k itself is assumed algebraically closed.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` in
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and `QuasiCompact` in
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `def-weil-proper-morphism`: `IsProper` in
  Mathlib.AlgebraicGeometry.Morphisms.Proper; its `IsSeparated` and
  `UniversallyClosed` dependencies were inspected as well.
- `def-pc-integral-scheme`: `IsIntegral` in Mathlib.AlgebraicGeometry.Properties.
- `def-weil-open-immersion`: `IsOpenImmersion` in Mathlib.AlgebraicGeometry.OpenImmersion.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  Mathlib.Topology.KrullDimension, including its subset/subspace interpretation.
- `def-sbc-smooth-morphisms`: `Smooth` in Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-connected-scheme`: `ConnectedSpace` in Mathlib.Topology.Connected.Basic,
  whose definition explicitly includes Nonempty.
- The existing landed definition node `def-sbc-normal-dominant-galois` is added to
  stmt_deps to cite `IsNormalScheme` from WeilConjectures.AlgebraicGeometry.NormalScheme.
  Its integral normal-scheme definition matches the combined normal AND integral
  conclusion of this item exactly. No node record other than the item's is changed.
- `Scheme.IdealSheafData.vanishingIdeal` and `.subscheme` are Mathlib's constructions,
  exposed by Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme. The recorded proof
  dependency `lem-weil-pbc-reduced-induced-closed-subscheme` supplies the expected
  reducedness, support and uniqueness properties in
  WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme.

All proof dependencies having recorded modules are imported as nonpublic imports.
Mathlib leaves for affine Noetherianity, closed-immersion properness, principal-ideal
height, and localization dimension are imported by their owning modules. The proof
node `lem-sfb-componentwise-normalization-generic-properties` currently has no recorded
Lean module, so there is none to import. It is not needed to type this statement.
No import cycle or duplicate declaration occurred in the wrapper compilation.

### Edge cases

- The empty scheme is excluded by the node's connected/nonempty hypotheses, encoded
  together by ConnectedSpace. It is not accidentally admitted as merely preconnected.
- A connected smooth zero-dimensional finite-type scheme over algebraically closed k
  is Spec k and is proper, so the nonproper hypothesis excludes dimension zero. The
  positive natural d is a conclusion, not an additional input assumption.
- A proper Y is excluded exactly by the input hypothesis. In particular the theorem
  does not demand a nonempty boundary for an already proper scheme.
- A^1 in P^1 has boundary dimension zero; d=1 gives d-1=0 correctly.
- A^2 in P^2 has a one-dimensional boundary. A proper smooth surface minus one point
  requires blowing up the puncture; the theorem allows this and imposes neither
  projectivity on Y nor smoothness of X.
- Mixed-dimensional boundaries of an initial compactification are allowed: it is
  the resulting completion whose every boundary component has dimension d-1.
- Arbitrary characteristic is retained. The algebraically closed field is perfect,
  and no characteristic-zero, rational-point, or quasi-projectivity binder is added.
- The one explicit universe u is shared by k and its schemes, as required by the
  existing Spec and Scheme interfaces; there are no test-object quantifiers in a
  smaller independent universe. Both autoImplicit options are disabled.

### Searches

All searches below were run for Q112 / lem-sfb-normal-divisorial-completion on
2026-10-24 before writing the module.

1. `msearch.py ... leanfinder "A smooth connected nonproper variety has a normal proper compactification with nonempty pure codimension one boundary"`:
   8 hits, including `IsIntegral.nonempty`, `IsIntegral`, `Scheme.Hom.normalization`,
   dominance into a normalization, and quasi-affine compactness. None asserts this
   normal proper divisorial completion; no one-line specialization supplies it.
2. `msearch.py ... loogle '"IsNormalScheme", "IsProper"'`: 0 hits.
3. `msearch.py ... grep 'compactification.*normal|normal.*compactification|divisorial.*completion|reducedBoundary' AlgebraicGeometry`:
   0 Mathlib hits.
4. `msearch.py ... leansearch "Normal proper compactification of a smooth connected nonproper scheme with boundary of pure codimension one"`:
   8 hits, consisting of the properness predicate, its constructor, normalization
   morphisms and their identities, and proper-map consequences of universal closedness.
   None gives the existence theorem with its boundary dimensions.
5. `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
   normal compactifications, divisorial completions and boundary/complement definitions:
   no declaration states the item. The existing normal smooth projective
   compactification module is restricted to dimension-one finite-field curves;
   it is not this theorem. NormalScheme gives the usable existing normal predicate.
   The reduced boundary is already constructed from `vanishingIdeal`, used in that
   compactification module and elsewhere; no duplicate definition was introduced.
6. `rg -n` on the proposed full declaration name and item id in Mathlib/project/upstream
   name records: no declaration collision. DAG searches found the existing
   `def-sbc-normal-dominant-galois` owner for IsNormalScheme.

No STATEMENT-DISPUTED issue or source-based correction is needed. The only item changes
are the `lean` record and addition of the existing normal-scheme definition to stmt_deps.

### Validation

`python3 /home/ubuntu/weil-launcher-all/batch2/scompile.py Q112 lem-sfb-normal-divisorial-completion <module>`
passed in sandbox mode (6.5 s) and the actual library module mode (8.9 s), with no
errors or non-sorry warnings. The module has one theorem and one `sorry`; every
universe and binder is explicit. The Lean signature in the node is copied verbatim
from the theorem keyword to before `:=`. JSON uses indent 1 and ensure_ascii false.

## Second reading by Q112

This is a direct-dispatch author self-check, not a claimed independent worker review;
the brief prohibits starting another agent and the maintainer independently reviews
the delivery. I reopened the complete node and the generated module after compilation.

Checked the input list in order: algebraically closed field; a specified k-structure;
separatedness; both finite-type factors; smoothness; connectedness with nonemptiness;
nonproperness. Checked the output list in order: integrality of Y; existence of X,
its k-structure and j; open immersion; normality with integrality in IsNormalScheme;
properness; the equation over k; density; nonemptiness of the canonical reduced
complement; the positive finite dimension of both schemes; the universal dimension
condition over all actual irreducible components of that complement. The positive
natural d makes the subtraction agree with dim Y minus one. No hypothesis or clause
is missing or stronger than the node. The added landed stmt_dep records the actual
normal-scheme definition used; it does not change the statement. No mismatch was
found and no mathematical statement was changed during this second reading.
