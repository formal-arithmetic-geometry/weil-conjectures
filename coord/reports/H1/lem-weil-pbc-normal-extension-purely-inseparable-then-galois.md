## Worker report

The module `Sheaf.FieldTheory.NormalExtensionFixedField` states
`Normal.fixedField_purelyInseparable_and_galois`, with its only proof `by sorry`.
It uses the existing Mathlib fixed intermediate field; it introduces no definition.

Hypotheses and clauses, in the order of the node:

- A field F and a field extension E/F are `(F : Type u) (E : Type v)` with
  `[Field F] [Field E] [Algebra F E]`. The structure map is `algebraMap F E`.
- Algebraicity and normality are exactly `[Normal F E]`. Mathlib's `Normal`
  extends `Algebra.IsAlgebraic F E` and requires every mapped minimal polynomial
  to split in E. Thus the node's two requirements are both present, without a
  separability or finite-degree assumption.
- The specified set E_insep is `let S := IntermediateField.fixedField
  (⊤ : Subgroup (E ≃ₐ[F] E))`. `IntermediateField.mem_fixedField_iff` says
  membership means every automorphism in this subgroup fixes the element;
  membership in the top subgroup puts no restriction on the automorphism.
- That this set is a subfield of E containing F is encoded by its type
  `IntermediateField F E`. This structure extends `Subalgebra F E`, including
  containment of the image of F, and adds closure under inverses. Its
  `toSubfield` and field/algebra instances are the inherited ones, not choices
  of a different carrier or structure. No extra theorem is needed to assert
  structure already carried by the exact Mathlib object.
- S/F is purely inseparable: `IsPurelyInseparable F S`.
- E/S is separable algebraic: `Algebra.IsSeparable S E`. This predicate already
  implies algebraicity (the zero minimal polynomial is not separable).
- E/S is normal: `Normal S E`. These last two clauses are precisely Galois by
  `isGalois_iff`, not a finite-Galois specialization.

Dependency declarations used:

- `def-pc-field-extension`: `Algebra`, Mathlib.Algebra.Algebra.Defs, with field
  instances, as its `mathlib_match` prescribes.
- `def-weil-algebraic-element`: `IsAlgebraic` and `Algebra.IsAlgebraic`,
  Mathlib.RingTheory.Algebraic.Defs, used through `Normal`'s algebraicity field.
- `def-weil-pbc-finite-purely-inseparable-extension`: `IsPurelyInseparable`,
  Mathlib.FieldTheory.PurelyInseparable.Basic. The dependency's text defines
  both purely inseparable extensions and finite ones. This item asks only for
  purely inseparable, so its optional `Module.Finite` notion is not imposed.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  Mathlib.FieldTheory.Separable, as recorded in its `mathlib_match`.

Other reused Mathlib notions: `Normal` (Mathlib.FieldTheory.Normal.Defs),
`IntermediateField` (Mathlib.FieldTheory.IntermediateField.Basic), and
`IntermediateField.fixedField` (Mathlib.FieldTheory.Galois.Basic).
Both imports are used; dependencies are Mathlib leaves and have no Sheaf module
requiring an import.

Source check: the local Stacks text is absent on this machine. Opened
https://stacks.math.columbia.edu/tag/030M and verified part (2) and its proof's
choice E_insep = E^{Aut(E/F)}. It agrees with the node. The declaration docstring
carries the node's six-step proof, including its named proof dependencies.

Edge cases checked mathematically before writing:

- E = F: the fixed field is all of E; both identity extensions have the required
  properties.
- Characteristic zero: the fixed field is the base field; the purely
  inseparable predicate correctly reduces to this case.
- Characteristic p, even when E/F is purely inseparable: all F-automorphisms
  are identity, so S = E, and the top extension is the separable normal identity
  extension.
- Infinite normal algebraic extensions and infinite automorphism groups are
  allowed; no finite dimension or finite group binder appears.
- Independent universes u and v allow arbitrary universes for the two fields.
  Fields are nontrivial; there is no omitted zero-field case.

Searches for an existing statement:

- `msearch.py ... leanfinder`: "For an algebraic normal field extension E/F the
  fixed field of all F-automorphisms is purely inseparable over F and E is
  Galois over this fixed field". Eight hits, including
  `IsGalois.of_fixed_field` (requires a finite group),
  `IsGalois.of_fixedField_normal_subgroup` (assumes the original extension is
  already Galois), and `InfiniteGalois.normal_iff_isGalois`. None states the
  whole result for a normal algebraic extension.
- `msearch.py ... loogle`: `IsPurelyInseparable, IntermediateField.fixedField`.
  No hits.
- `msearch.py ... grep` in FieldTheory:
  `fixedField.*IsPurelyInseparable|IsPurelyInseparable.*fixedField|fixedField_top|class Normal`.
  Three hits: `Normal` and finite-Galois `fixedField_top` uses; no match.
- `rg` in all upstream WeilConjectures and project lean/Sheaf for `fixedField`
  and `purelyInseparable`: upstream hits use fixed fields for ramification and
  invariants; project results concern open-subgroup fixed fields and finite
  purely inseparable constructions, not this statement.
- `rg` for the node id in upstream WeilConjectures: no hits.
- `rg` for the proposed full declaration name in Mathlib, upstream source,
  project Lean and dag/lean_names_upstream.json: no hits (name available).

No statement correction, new node, unusable dependency, or disputed statement
was found. The server compile completed cleanly in 1.5 seconds (exit code 0).

## Second reading by H1

I independently read the sandbox node and module, all four statement dependency
nodes and their recorded Mathlib declarations, and the source statement and proof.
The local Stacks checkout is absent. I read the original `fields.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/fields.tex,
label `lemma-normal-case`, and https://stacks.math.columbia.edu/tag/030M.
The lemma introduces a normal algebraic field extension, with no extra ambient
hypotheses. Part (2) is the asserted tower, and the proof specifies the fixed
field used here. Parts (1) and (3) are outside this node's statement.

Object/hypothesis/conclusion checklist, in node order:

1. Base field F: `(F : Type u) [Field F]`. Exact.
2. Field extension E/F: `(E : Type v) [Field E] [Algebra F E]`.
   Read `Algebra` in Algebra/Algebra/Defs.lean: its `algebraMap` supplies the
   ring homomorphism in def-pc-field-extension; for fields it is injective.
   No field, ring, or map has been replaced. Exact.
3. Algebraicity of every element and splitting of every minimal polynomial:
   `[Normal F E]`. Read Normal/Defs.lean: the class extends
   `Algebra.IsAlgebraic F E` and its `splits'` field says the mapped minimal
   polynomial of each x splits in E. Read Algebraic/Defs.lean: `IsAlgebraic`
   is a nonzero annihilating polynomial, and `Algebra.IsAlgebraic` quantifies
   over every element. Thus both node hypotheses, and no separability or
   finite-degree assumption, are present. Exact.
4. The specified fixed set E_insep: `let S := IntermediateField.fixedField
   (⊤ : Subgroup (E ≃ₐ[F] E))`. Read Galois/Basic.lean definitions
   `FixedPoints.intermediateField`, `IntermediateField.fixedField` and
   `mem_fixedField_iff`: membership is `∀ f ∈ ⊤, f x = x`, precisely every
   F-algebra automorphism fixing x. No finite or closed-subgroup restriction.
   This is the specified set, not an unspecified existential witness. Exact.
5. Subfield of E containing F: the preceding object has type
   `IntermediateField F E`. Read IntermediateField/Basic.lean: it extends
   `Subalgebra F E` with inverse closure, its `toSubfield` has the same carrier,
   and `algebraMap_mem` supplies containment of F. Its `toField`, `toAlgebra`
   and inherited base algebra provide the canonical tower on this same set.
   Encoding these structural conclusions in the existing bundled object is
   exact and needs no extra proposition or private definition.
6. S/F purely inseparable: first conjunct `IsPurelyInseparable F S`.
   Read PurelyInseparable/Basic.lean, especially
   `isPurelyInseparable_iff_pow_mem` (Stacks 09HE): in exponential
   characteristic q every element has a q^n power in the base image.
   This specializes to the dependency node's p-power condition in positive
   characteristic and equality with the base image in characteristic zero.
   The dependency also defines finite extensions, but this node does not
   require that optional condition; no `Module.Finite` belongs here. Exact.
7. E/S separable algebraic: second conjunct `Algebra.IsSeparable S E`.
   Read Separable.lean: every minimal polynomial is separable; its
   `isAlgebraic` instance proves this already includes algebraicity, since
   the zero minimal polynomial is not separable. This is the declaration
   recorded by def-weil-pbc-separable-algebraic-extension. Exact.
8. E/S normal, hence Galois: third conjunct `Normal S E`.
   This uses the canonical inclusion algebra of S into E. Read
   `isGalois_iff` in Galois/Basic.lean: the last two conjuncts are exactly
   `IsGalois S E`, without a finite-dimensional requirement. Exact.

Edge cases: independent universes u and v are explicitly bound, and S is a
subtype of E, so no size restriction is introduced. Fields exclude the zero
ring already in the source; there is no empty-field case. E = F gives the
identity tower. A purely inseparable E/F has only the identity automorphism,
so S = E and the top extension is identity. In characteristic zero S is the
base image and E/F may be any infinite Galois extension. In positive
characteristic the exponent n = 0 is allowed by the standard predicate.
Infinite degree and infinite automorphism groups remain allowed. No index
set, scheme, or additional natural-number parameter occurs.

Independent searches, using different wording from the first reader:

- LeanFinder via msearch: "An algebraic normal extension is separable over
  the subfield invariant under every base field automorphism, and that
  invariant subfield is radicial over the base". Eight results including
  `separableClosure.isGalois`, `separableClosure.isPurelyInseparable`,
  `IsPurelyInseparable.normal`, and `isGalois_iff`. The separable-closure
  tower puts the two extension properties in the opposite order, so does
  not state this node.
- Loogle via msearch: `Normal, IsPurelyInseparable`. Only
  `IsPurelyInseparable.normal`, the reverse implication, not this statement.
- LeanSearch via msearch: "For a normal algebraic extension the automorphism
  invariant subfield is purely inseparable and the extension over it is
  Galois". Service unavailable (Internal Server Error); no verdict inferred.
- Grep via msearch for `fixedPoints|perfectClosure|fixedField` was too broad
  (hits in dynamics). Followed with direct rg for invariant fields,
  `normal.*insepar`, `insepar.*normal`, `fixedField`, and
  `FixedPoints.intermediateField` across Mathlib FieldTheory/Galois and
  PurelyInseparable, all upstream WeilConjectures, and all project lean/Sheaf.
  Opened the actual nearby candidate `IsGalois.of_fixed_field`: it requires
  a finite acting group. The normal-subgroup Galois correspondence assumes
  an already Galois base extension. Neither supplies this whole statement.
  Project matches concern open subgroups of absolute Galois groups, and
  upstream matches concern ramification or invariant rings. None states
  this node. The proposed declaration name and blueprint id have no matches
  in upstream, project Lean, or dag/lean_names_upstream.json.

No H3/H4 mismatch found. No new definition node, dependency module, or statement
correction is needed. There is one named theorem with `by sorry`, no definition
with postponed data, and no proof has been supplied. The module and declaration
docstrings name Stacks 030M and this blueprint id; the declaration reproduces
all six proof steps and their named dependencies. Both imports are used, lines
are within 100 characters, and all variables and universes are explicitly bound.
The node's `lean.statement` is verbatim the module signature before `:=`.
I left the correct Lean and node unchanged; only this second-reading report
was appended. Validation: server single-file compile and delivery preflight.
