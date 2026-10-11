## Worker report

Module: `Sheaf.AlgebraicGeometry.QuasiFiniteAffineOpenInFinite`.
Declaration: `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_isQuasiFinite_affine`.
This states Stacks Project, Morphisms, Tag 03GU, with the five-step natural-language
proof from the DAG in its docstring. Its only proof is `sorry`, as required in stage 2.

The source statement was read at https://stacks.math.columbia.edu/tag/03GU; the local
literature/stacks-project/morphisms.tex is absent on this machine. The online statement
agrees exactly with the node. No statement correction or disputed statement is needed.

Clause-by-clause correspondence:
- Schemes X and Y: `{X Y : Scheme.{u}}`, with arbitrary explicit universe `u`.
- A morphism f : Y → X: `(f : Y ⟶ X)`.
- X and Y affine: `[IsAffine X] [IsAffine Y]`.
- f quasi-finite: `(hf : f.IsQuasiFinite)`, using the recorded Stacks predicate.
  Its definition requires locally finite type, quasi-compactness (together finite type),
  and openness of every singleton `{f.asFiber x}` in its scheme-theoretic fibre.
- There exists a scheme Z: `∃ (Z : Scheme.{u})`.
- The two morphisms: `(j : Y ⟶ Z) (π : Z ⟶ X)`.
- Z affine: `IsAffine Z`.
- j an open immersion: `IsOpenImmersion j`.
- π finite: `IsFinite π`.
- f = π ∘ j: `f = j ≫ π`, the categorical order of composition.
The parenthetical ring construction in the node explains the source proof, rather than
adding conditions to the existential conclusion; it is included in the docstring proof.

Dependency declarations inspected and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  morphisms are locally ringed-space morphisms.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`, defined by
  the canonical map to Spec of global sections being an isomorphism. This is the
  affine clause of def-pc-scheme; it is available through the finite-morphism import.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`: `Scheme.Hom.IsQuasiFinite`, the
  pqf-def-quasifinite declaration, read with its full definition and docstring.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  the exact mathlib_match of def-weil-open-immersion.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`, extending
  IsAffineHom and requiring finite ring maps on every affine open, as recorded for
  def-weil-finite-integral-morphism. The unused integral clause is not restated.

Edge cases checked: empty schemes are permitted, including Y empty and X empty.
For empty Y one can take Z = X, π the identity and the empty open immersion j;
if X is empty then Y is empty as well. No nonemptiness, domain, Noetherian, separated,
finite-presentation, field, or characteristic condition is introduced. Affine schemes
can have nilpotents and zero rings. The intermediate Spec of a finite subalgebra of
Γ(Y, ⊤) lies in the same universe `u`, so that binder excludes no case of the node.

Searches (2026-10-11; raw msearch outputs also in searches.jsonl):
- msearch leansearch: “A quasi-finite morphism of affine schemes factors as an open
  immersion followed by a finite morphism”; service unavailable (Internal Server Error).
- msearch leanfinder: “A quasi-finite morphism between affine schemes factors through
  an open immersion into an affine scheme finite over the target”; eight hits including
  locallyQuasiFinite_iff, quasiFinite_appLE, isFinite_iff, locallyOfFiniteType_iff,
  IsFinite.toIsAffineHom, instLocallyQuasiFiniteOfIsImmersion,
  Scheme.IsQuasiAffine.of_isAffineHom, and finiteType_appLE; none states the node.
- msearch loogle: `AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.IsAffine`; zero hits.
- msearch grep in AlgebraicGeometry: `exists.*(isOpenImmersion|isFinite)|03GU|
  quasi.finite.affine`; three hits, on local finite restrictions and local isomorphisms,
  with no affine factorization statement.
- rg in WeilConjectures and lean/Sheaf: `03GU|quasi.finite.affine|
  exists.*isOpenImmersion.*[Ff]inite`; upstream has the general Tag 05K0 theorem
  `Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite`, inspected with
  its docstring and full signature. It assumes local quasi-finiteness, local finite
  type, separatedness, quasi-compactness, and qcqs target, and concludes a factorization
  with quasi-compact j, without explicitly stating affine source, target, or Z.
  It is a useful proof ingredient, but is not this node's statement. The Tag 0F2N
  finite-presentation variant and the affine-morphism factorization were also inspected;
  neither is exact. Existing Sheaf hits concern related affine-pair and bounded-fibre
  lemmas, not this statement.
- rg for the exact item id in WeilConjectures: no hits.
- rg in dag/lean_names_upstream.json: no 03GU/affine-quasi-finite factorization match.
- rg for the proposed full declaration name in Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json: no hits, so the name is fresh.

No new nodes or dependency modules were needed. Every import supplies a notion in the
statement; all variables and universes are explicitly bound. Compilation and the dry-run
preflight are run on the server by the prescribed launcher scripts.

## Second reading by K1

I reread the node statement and the declaration line by line against Stacks Project,
Morphisms, Lemma 03GU (with Algebra Lemma 00QB as its proof source). The objects and
hypotheses match: schemes `X Y : Scheme.{u}`, affine instances `[IsAffine X]` and
`[IsAffine Y]`, a morphism `f : Y ⟶ X`, and `hf : f.IsQuasiFinite`. The conclusion
introduces `Z : Scheme.{u}`, `j : Y ⟶ Z`, and `π : Z ⟶ X`, followed by exactly the
four clauses `IsAffine Z`, `IsOpenImmersion j`, `IsFinite π`, and `f = j ≫ π`.
The final equality is the categorical rendering of the source's `f = π ∘ j`.
No hypothesis, object, quantifier, or conclusion clause is added, dropped, weakened,
or strengthened.

The edge cases remain covered: the common universe does not exclude affine schemes,
empty schemes or zero rings; no nonemptiness, Noetherian, separatedness, characteristic,
or finite-presentation assumption is present; and `f = j ≫ π` has the required order.
The source's affine intermediate scheme is represented by the existential `Z` and does
not add a hypothesis to the theorem.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` using LeanSearch, LeanFinder,
Loogle, and `rg` for the declaration and the 03GU/global affine factorization. The
nearest existing results are local Zariski-main and quasi-finite lemmas; none states
this affine scheme factorization. The recorded dependency declarations were opened
and are the notions used by the imports; no dependency module or new definition node
is needed. The first worker's statement and module were correct, so the second reading
made no code or node changes. The module compiles cleanly with the required `sorry`
proof only.
