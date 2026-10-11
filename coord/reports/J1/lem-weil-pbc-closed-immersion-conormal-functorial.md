## Worker report

The module states functoriality of the conormal sheaf for a commutative square of closed
immersions. `i'.ker.comap g ≤ i.ker` renders containment of the extended ideal. The
existential `γ` is the induced map on tensor-pullback ideal modules; its section equation
uses the chosen `exists_tensorPullbackAdjunction g` unit and says that inclusion after `γ`
equals the pullback of the inclusion. The unique `c` is the map between the two pulled-back
conormal modules. Its displayed equality uses the units for `i'`, `f`, `g`, the pushforward
composition isomorphism, and `pushforwardCongr h.symm`, rendering the canonicality and the
commutative-square identification.

The hypotheses are exactly schemes `X,Z,X',Z'`, closed immersions `i,i'`, morphisms `g,f`,
and `i ≫ g = f ≫ i'`. The two conclusion clauses are ideal containment and the induced
canonical maps, with the module morphism equations recording their definitions.

Dependencies used: `Sheaf.AlgebraicGeometry.AffineConormalSections`, especially
`AlgebraicGeometry.Scheme.Modules.affine_conormal_sections`; `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`
via `exists_tensorPullbackAdjunction`; Mathlib `Scheme.IdealSheafData.comap`,
`Scheme.Hom.ker`, `Scheme.Modules.pushforwardComp`, `Scheme.Modules.pushforwardCongr`, and
`IsClosedImmersion`.

Edge cases checked: identity square (`f = g = 𝟙`) has identity ideal containment; zero ideal
has zero conormal map; and the empty affine ideal is handled by the same kernel and tensor
pullback expressions. The statement is intentionally universe-polymorphic in one scheme
universe, as all four schemes in the source diagram share a universe.

Searches: `msearch.py leanfinder 'Functoriality conormal sheaf closed immersion commutative square of schemes'`
returned only Mathlib closed-immersion lifts and pullback lemmas, no conormal sheaf map;
`msearch.py loogle 'Ideal.mapCotangent'` found the affine `Ideal.mapCotangent` only; grep of
Mathlib, source `WeilConjectures`, and project `lean/Sheaf` found no existing theorem matching
this scheme-level statement. The node's recorded Lean searches likewise found no match.

No `STATEMENT-DISPUTED`.

## Dependency modules

`def-weil-closed-immersion` was unusable as a bare Mathlib class record because its node
also specifies the affine quotient characterization. `closedImmersion_iff_components`
records the defining closed-embedding and surjective-stalk formulation used by that node.
`def-sbc-closed-immersion-ideal-sheaf` needs the sheaf-module object, whereas Mathlib's
`Scheme.Hom.ker` is ideal-sheaf data; `idealSheafModule` states its kernel module form.

## Earlier second reading (a previous round; superseded)

I reread the node and all three delivery modules. The schemes, closed-immersion instances,
commuting-square equation, ideal containment, induced `γ`, and unique conormal map `c` all
appear in the theorem signature. The dependency modules state the closed-immersion predicate
and kernel ideal sheaf module used by the theorem. No mismatch was found.

## Second reading by J1

Independent reading of the node, its seven statement dependencies, their recorded
signatures, and the delivered Lean. The earlier second-reading paragraph above is
superseded by this reading and the repairs below.

Source checked: Stacks `morphisms.tex`, section "Conormal sheaf of an immersion",
Definition 01R2, Lemma 01R3 and Lemma 01R4, including all three proof paragraphs.
The local literature checkout lacks this file; I read the available Stacks TeX at
`/home/ubuntu/c1-stacks-review/morphisms.tex` (lines 6139–6275) and `schemes.tex`
(Definition 01HK and Lemma 01IN). The source's general immersion statement is being
specialized to closed immersions exactly as the node says. No ambient Noetherian,
finite-type, base-field or characteristic assumption is made in that section.

Object/hypothesis/conclusion checklist, with the final Lean open:

1. Four arbitrary schemes X, Z, X', Z': `{X Z X' Z' : Scheme.{uc}}`.
   Verdict: exact; no affine or nonempty scheme assumption.
2. Closed immersions i:Z→X and i':Z'→X': the two morphism binders and
   `[IsClosedImmersion i] [IsClosedImmersion i']`. Verdict: exact. Read Mathlib's
   class in Morphisms/ClosedImmersion.lean: closed embedding plus surjective stalks;
   `isClosedImmersion_iff_isAffineHom` gives the affine quotient characterization.
3. Their kernel ideals I and I': `i.ker` and `i'.ker`, with sheaf-module forms
   `i.ker.toModules` and `i'.ker.toModules`. Verdict: exact. Read `Hom.ker` and
   `Hom.ker_apply`: the latter applies since closed immersions are affine and
   quasi-compact. Read upstream IdealSheaf/Module.lean `toModules` (kernel module),
   `toModulesι`, `range_toModulesι_app`, and `injective_toModulesι_app`.
   These are the existing ideal modules, with their actual inclusions.
4. Conormal sheaves i*I and i'*I': `(tensorPullback i).obj i.ker.toModules`
   and `(tensorPullback i').obj i'.ker.toModules`. Verdict: exact. Read the
   tensorPullback dependency's tensor-formula definition and the signature and
   docstring of `affine_conormal_sections`: it identifies these modules with I/I²
   on inverse images of affine opens, by the unit on ideal representatives.
5. Arbitrary g:X→X' and f:Z→Z': `(g : X ⟶ X') (f : Z ⟶ Z')`.
   Commutativity g∘i=i'∘f: `(h : i ≫ g = f ≫ i')`. Verdict: exact.
6. Extended ideal I'O_X contained in I: `i'.ker.comap g ≤ i.ker`.
   Verdict: exact. Read the extended-ideal dependency and Mathlib's `comap`,
   the kernel of the base-change closed immersion; this is the extended ideal.
7. The induced O_X-linear gamma:g*I'→I: existential `γ` with the displayed
   equality after `toModulesι` on every section pulled back by the g-unit.
   Verdict: exact. The unit is the canonical tensor unit specified by
   `exists_tensorPullbackAdjunction`, not an arbitrary adjunction. Its images
   locally generate the tensor pullback, so the section equation fixes gamma.
8. Canonical O_Z-linear c:f*i'*I'→i*I: the `∃! c` morphism binder, followed by
   the equality of morphisms from I' to (i≫g)_*i*I. The left side is the adjoint
   of c after the i' and f units; the right side is the adjoint of i*gamma.
   `pushforwardComp` implements composition and `pushforwardCongr h.symm`
   identifies f≫i' with i≫g. Read both definitions and their section formulas.
   Verdict: exact canonical composite and uniqueness, without demanding flatness.
9. Every affine pair U,U' with g(U)⊆U': final binders
   `(U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1)`.
   Verdict: exact. R,R' can be their actual section rings; arbitrary coordinate
   ring isomorphisms transport this formula, as in `affine_conormal_sections`.
10. On these opens g-sharp sends I' into I: for each ideal section s', the
    final `∃ s` satisfies `toModulesι s = g.appLE ... (toModulesι s')`.
    Verdict: explicit affine containment. `appLE` is precisely the ring map
    on the specified pair of opens, not just on the full inverse image.
11. Affine quotient map a mod I'² ↦ g-sharp(a) mod I²: the final equation
    evaluates the i'/f-unit/c composite on s', identifies its target using h,
    and restricts by `val.map (homOfLE (i.preimage_mono H)).op` to Z∩U.
    It equals the i-unit of s. Verdict: exact on every ideal representative.
    By the recorded affine-conormal dependency, those unit values are exactly
    their quotient classes; all quotient classes have such representatives.
    Thus the clause covers all of I'/I'² and states the claimed quotient formula,
    without duplicating the dependency's canonical equivalences. Together with
    local generation of f*C' this also characterizes the sheaf map.

Repairs: the initial signature expressed the canonical composite by adjunction,
but never explicitly quantified over the affine pair or stated its `g.appLE`
section formula. Added the final affine clause under the same `∃! c` predicate;
it follows the node's existing conclusion and introduces no new hypothesis.
The natural-language node statement and its dependencies were not changed.
Updated `lean.statement` verbatim to the final signature. Fixed the parenthesis
in that new formula after the first compile; the next compile was clean.

Also removed BOTH proposed dependency modules and their sandbox node copies.
`def-weil-closed-immersion` already has a usable exact Mathlib match; the delivered
`closedImmersion_iff_components` was a redundant restatement of the class and did
not even add the affine characterization that its note claimed was missing.
`def-sbc-closed-immersion-ideal-sheaf` already records `Hom.ker` with the explicit
note to use `i.ker.toModules`. The proposed `idealSheafModule` merely renamed that
existing module and was never used by the main theorem. These were H4/H13 faults,
not missing notions. The earlier "Dependency modules" report section describes
those removed drafts only; the final delivery has no dependency modules and no
new definition nodes.

Edge cases: empty schemes and the empty affine open are allowed (no nonemptiness
binders); zero ideals give zero conormal modules and the unique zero map; identity
closed immersions and identity squares are allowed. No natural-number, index-set,
characteristic, field or dimension parameter is present. Universes are bound by
`universe uc`; all four schemes and their arrows live in the same Scheme category,
as required by Mathlib, and uc is arbitrary. No finiteness or small test-object
quantification has been introduced. All other variables are explicit binders.

Independent searches (2026-10-11):
- LeanSearch via msearch: "Functorial map of conormal sheaves of closed immersions
  induced by commutative square"; service unavailable (Internal Server Error),
  recorded as unavailable, no search verdict inferred.
- LeanFinder via msearch: "natural morphism between conormal modules for a
  commuting diagram of immersions"; eight hits, only immersion restriction,
  closed-immersion lifts, and subscheme maps, no conormal sheaf map.
- Loogle via msearch: `Ideal.mapCotangent`; four ring-level declarations, with
  the principal signature `I₁.Cotangent →ₗ[R] I₂.Cotangent`. This is not the
  scheme-level statement and cannot replace the sheaf morphism.
- rg on Mathlib AlgebraicGeometry and RingTheory/Ideal/Cotangent.lean, source
  WeilConjectures, and project lean/Sheaf, using `conormal`, `mapCotangent`,
  `idealSheafModule`, and `closedImmersion_conormal_functorial`: the recorded
  affine calculation, diagonal conormal and ring-level statements occur, but
  no existing theorem states this commuting-square conormal functoriality.
  Read relevant definitions directly rather than trusting names/search hits.

Final module has its source/blueprint docstrings and all four node proof steps,
only one named theorem with `sorry`, no new definitions and no hollow data.
No statement correction record exists or is needed; no citer statement changes.
No STATEMENT-DISPUTED. Server single-file compile: exit 0, 2.2 seconds, no warnings.
