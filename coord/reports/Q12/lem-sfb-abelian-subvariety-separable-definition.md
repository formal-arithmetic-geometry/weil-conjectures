## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.SubvarietySeparableDefinition`
states `AlgebraicGeometry.IsAbelianVariety.exists_finiteGalois_subvariety_definition`.
Its only theorem has proof `sorry`; no definitions, axioms, helper theorems or new
nodes are introduced. The accepted stage-1 split is preserved verbatim. The inherited
BLOCKED ending concerned a stage-1 split, not this stage-2 statement; the stage-handoff
paragraph of coord/brief-stage2.md §0 explicitly directs this continuation.

Source checked: Milne, Abelian Varieties, January 2, 2022,
https://www.jmilne.org/math/xnotes/AVs.pdf, Section 12, second unnumbered lemma
following Proposition 12.1, printed p.19 (PDF page 19). It states finite separable
definition for every geometric abelian subvariety over any field. Enlarging to the
finite normal closure inside the fixed algebraic closure gives finite Galois
definition, by further base change. The older local source is
literature/milne-abelian-varieties_AV.pdf, I Section 10, printed pp.42–43.
The newer article is still WANTED as a local literature asset; it was read online
for this delivery, without changing the read-only repository.

Clause matching:

- The field k is `(k : Type u) [Field k]`.
- The fixed algebraic closure is `(Ω : Type u) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]`. This allows an arbitrary chosen algebraic closure, not only
  Mathlib's particular `AlgebraicClosure k`.
- The abelian variety A/k is `(A : Over (Spec (.of k))) [GrpObj A]
  [IsAbelianVariety A]`. The definition separately requires the group structure;
  its predicate provides properness, smoothness and connectedness.
- The geometric abelian variety C is `(C : Over (Spec (.of Ω))) [GrpObj C]
  [IsAbelianVariety C]`.
- Its given closed subgroup inclusion into A_Ω is
  `i : C ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj A`
  with `[IsClosedSubgroupScheme i]`. The group structure on the ambient base change
  is the actual transported structure `Functor.grpObjObj`, activated with
  `open scoped CategoryTheory.Obj`; no arbitrary group structure is supplied.
- The intermediate field is `E : IntermediateField k Ω`. Its canonical algebra
  and `E.subtype : E →+* Ω` supply the two inclusions of the field tower.
- Finiteness is `FiniteDimensional k E`; separable algebraic and normal are
  `IsGalois k E`, whose two fields are exactly `Algebra.IsSeparable k E` and
  `Normal k E`. The latter contains algebraicity and splitting of each minimal
  polynomial over k in E, as the node specifies.
- The descended abelian variety is existential `C_E : Over (Spec (.of E))`, its
  `GrpObj C_E`, and `IsAbelianVariety C_E`.
- Its closed subgroup inclusion into A_E is the existential `j`, with exactly
  `[IsClosedSubgroupScheme j]`, for the same `Over.pullback` construction.
- Scheme-theoretic scalar-extension equality is expressed without requiring
  literal equality of chosen representatives: `q : C.left ⟶ C_E.left` and
  `IsPullback q C.hom C_E.hom (Spec.map (CommRingCat.ofHom E.subtype))` identify C
  with `(C_E)_Ω` over Ω. The concluding equation says that `q ≫ j.left` followed
  by the projection from A_E to A equals `i.left` followed by the projection from
  A_Ω to A. Along with the structure maps, this makes the identification commute
  with the inclusions into A_Ω by its pullback universal property. Consequently
  it is the same closed subscheme, not just an abstract isomorphism or equality
  of geometric points. Since both inclusions are group homomorphisms and closed
  immersions, their induced group laws also agree under this identification.
- No perfectness, characteristic, dimension or positivity hypothesis is imposed.

Dependencies used, full signatures and docstrings read in the local source:

- `def-weil-field`: Mathlib.Algebra.Field.Defs, `Field`.
- `def-weil-algebraic-closure`: Mathlib.FieldTheory.IsAlgClosed.Basic,
  `IsAlgClosure` and `IsAlgClosed`; its recorded match explicitly permits
  `[IsAlgClosure k Ω]` for a fixed arbitrary closure.
- `def-sc-abelian-variety`:
  WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs,
  `AlgebraicGeometry.IsAbelianVariety`.
- `def-sc-group-scheme-subgroup`:
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs,
  `AlgebraicGeometry.IsClosedSubgroupScheme` (extends `IsSubgroupScheme`, which
  extends `IsMonHom`).
- `def-weil-pbc-separable-algebraic-extension`: Mathlib.FieldTheory.Separable,
  `Algebra.IsSeparable`, used as the separability field of `IsGalois`.
- `def-pc-base-change`:
  WeilConjectures.AlgebraicGeometry.BaseChangeConventions, whose documentation
  explicitly prescribes `Over.pullback` for scheme and morphism base change;
  `pullback.fst` is its ambient projection. `IsPullback` uses the same fibre
  product universal property and avoids incidental choices of representatives.

The Mathlib `Normal` and `IsGalois` definitions were also read, including their
fields, as was `Functor.grpObjObj` and its scoped instance. All universes and
variables are explicitly bound; `set_option autoImplicit false` enforces this.
One common ambient scheme universe includes arbitrary set-sized fields and
schemes by raising the common universe when necessary; there is no equality
between independently fixed universe parameters or a small test-object restriction.

Proof imports include the published torsion and geometric-reducedness modules,
the separable-closure module, Galois closure, faithfully flat field-extension
and descent tools, and Noetherian finite-type tools. The proof dependencies
`lem-sfb-abelian-field-extension`, `lem-sfb-abelian-prime-to-torsion-dense` and
`lem-sfb-dense-rational-closed-subscheme-descent` have no recorded Lean module
at the time of reading; they are not needed to state the theorem. Their
natural-language uses remain in the full five-step proof docstring and DAG.

Edge cases checked before writing:

- C can be the identity subgroup (dimension zero), or all of A_Ω: no nontriviality
  or proper-containment condition was added. E=k is permitted.
- A can be the zero-dimensional trivial abelian variety. Its nonemptiness comes
  from the original connected group-variety interface, not a new hypothesis.
- Characteristic zero and every positive characteristic are included.
- Imperfect k is included: there is no `PerfectField k` or separability condition
  on Ω/k, which can be inseparable. Only the existential E/k must be Galois.
- Already algebraically closed k is included and admits E=k.
- The cartesian-square condition excludes replacing C by a subgroup having only
  the same underlying topological subset: it fixes the full scheme structure.
- Abstract isomorphic subvarieties with a different image do not pass the
  ambient-compatibility equation. Compatibility of group laws follows from
  compatibility of the closed subgroup inclusions, so it is not discarded.

Searches run through the required wrapper:

- LeanFinder: `Every geometric abelian subvariety of an abelian variety over an
  arbitrary field descends to a finite Galois extension` — 8 hits, all field
  theory (`IsAbelianGalois` and tower/instance facts); no geometric descent.
- LeanSearch: `An abelian subvariety over an algebraic closure descends to a finite
  separable extension` — 8 hits, separable-closure and abelian Galois facts;
  no abelian-variety descent declaration.
- Loogle: `"IsAbelianVariety", "IsGalois"` — 0 hits.
- Mathlib grep: `IsAbelianVariety|abelianSubvariety|separable.*descent` in
  AlgebraicGeometry — 0 hits.
- Direct rg of lean/WeilConjectures and lean/Sheaf for
  `separable.definition|separable_definition|field.of.definition|fieldOfDefinition|abelian.*[Ss]ubvariety|abelianSubvariety`
  found only unrelated coefficient fields of definition and no target statement.
- Direct grep for the exact node id in lean/WeilConjectures returned no result.
  A final rg of both source trees and dag/lean_names_upstream.json for the theorem
  name, node id and `(separab|Galois).*subvariety` variants returned no match.

Validation: scompile.py compiled the delivered file in both its sandbox probe
and actual library module mode, with no errors or warnings (22.1 s / 16.5 s).
The module's first command is `module`, statement imports are public, proof
imports are private, and all lines are at most 100 characters.

No node fault or STATEMENT-DISPUTED issue was found. No statement correction,
new node or dependency-interface repair was needed.

## Second reading by Q12

A separate reading of the finished node and Lean file checked each binder and
conjunct against the clause list above. This is the worker's own second pass;
no second agent was started, as instructed. The maintainer supplies independent
review. In particular the two pullback legs are q and C.hom, the bottom/right
legs are C_E.hom and Spec(E → Ω), in the argument order required by IsPullback.
The ambient equation has target A.left on both sides and is accompanied by the
Ω-structure map, so it determines equality inside A_Ω, rather than equality in
A after forgetting Ω. The group-object existentials precede the subgroup
predicate, and the base-change group structures use the actual monoidal pullback.
The finite-dimensional and Galois conjuncts permit the trivial intermediate
field, and the hypotheses impose no perfectness. No mismatch or subsequent
statement change was found on this reading.
