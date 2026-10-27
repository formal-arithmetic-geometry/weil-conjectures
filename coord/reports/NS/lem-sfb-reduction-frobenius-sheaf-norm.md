## Worker report

The module `Sheaf.AlgebraicGeometry.ReductionFrobeniusSheafNorm` states
`AlgebraicGeometry.Scheme.reduction_frobenius_sheaf_norm` with one `sorry` and no
new definitions. The item is unchanged outside `lean`; no statement correction,
new node, or dependency repair was needed. Sources read: Stacks `divisors.tex`,
Tag 0BDZ (`lemma-Frobenius-gives-norm-for-reduction`) and Tag 0BCX
(`section-norms`). The declaration docstring carries all six steps of the node's
proof, including local lifts on arbitrary intersections and the empty-open case.

Hypothesis and clause correspondence:

- Prime `p`: `(p : ℕ) (hp : p.Prime)`.
- Scheme `X`: `(X : Scheme.{u})`, with an explicit unrestricted universe `u`.
- Noetherian, in the finite affine-cover sense: `[IsNoetherian X]`. Mathlib's
  class is locally Noetherian plus compact; finite Noetherian affine covers
  imply this and compactness extracts such a cover in the converse direction.
- `p O_X = 0` in every local ring: `hchar : ∀ x : X,
  (p : X.presheaf.stalk x) = 0`, literally the node's stalkwise assumption.
- Nilradical, reduction, and its immersion: `X.nilradical`,
  `X.nilradical.subscheme`, and `X.nilradical.subschemeι`, respectively.
- One uniform integer `e ≥ 1`: `∃ e : ℕ, 1 ≤ e ∧ ...`; this precedes the family
  quantified over all opens, so it cannot vary with the open.
- Unital ring homomorphisms on every open: `∃ ν : ∀ V : X.Opens,
  Γ(X.nilradical.subscheme, X.nilradical.subschemeι ⁻¹ᵁ V) →+* Γ(X, V)`.
  The `→+*` type includes additivity, multiplicativity, zero, and one.
- Compatibility with restriction: the first conjunct quantifies `V W hVW b`
  and equates restriction of `ν W b` with `ν V` of the restricted `b`.
  The preimage inclusion is the existing `Scheme.Hom.preimage_mono`.
- `ν_V(i^sharp a) = a^(p^e)`: the second conjunct is exactly
  `ν V (X.nilradical.subschemeι.app V a) = a ^ (p ^ e)`.
- On EVERY affine open, the quotient formula: the third conjunct quantifies
  `U : X.affineOpens` and `a : Γ(X, U.1)`, applies `Ideal.Quotient.mk` to `a`,
  transports it by `(X.nilradical.subschemeObjIso U).inv`, and states that
  `ν U.1` sends this class to `a ^ (p ^ e)`. The quotient ideal
  `X.nilradical.ideal U` is definitionally the radical of the zero ideal:
  `Scheme.nilradical = IdealSheafData.radical ⊥`. The quotient map is
  surjective, so quantifying representatives covers every quotient element.
  This uses the recorded canonical quotient isomorphism, not a chosen map.
- Residue-field vanishing: the fourth conjunct quantifies every `V`, `b`,
  `y : X.nilradical.subscheme` and membership proof `hy`; it says evaluation
  of `b` at `y` being zero implies evaluation of `ν V b` at `i(y)` being zero.
  Both evaluations are Mathlib's `Scheme.evaluation`, namely germ followed
  by the residue map. `hy` also witnesses `i(y) ∈ V` by definition of preimage.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, whose
  locally ringed space has affine neighbourhoods at every point, and
  `AlgebraicGeometry.Scheme.Hom` / `Hom.app` for the immersion and its comorphism.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, every ideal
  finitely generated. `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian`,
  extending `IsLocallyNoetherian` and `CompactSpace`; this supplies the
  scheme formulation of the same finite-cover condition.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` (and its public Basic import):
  `Scheme.nilradical`, `IdealSheafData.subscheme`, `subschemeι`, and
  `subschemeObjIso : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) ≅
  CommRingCat.of (Γ(X, U) ⧸ I.ideal U)`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, and `Scheme.evaluation`; these use the residue
  field of the actual local stalk, with its canonical induced field map.
- Proof import `WeilConjectures.AlgebraicGeometry.Curve.ReductionNilradicalNilpotence`:
  `Scheme.exists_nilradical_pow_succ_eq_bot (X : Scheme.{u}) [IsNoetherian X] :
  ∃ n : ℕ, X.nilradical ^ (n + 1) = ⊥`.
- Proof import `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`:
  `iterateFrobeniusOfPrime (R : Type*) [CommRing R] {p : ℕ}
  (hp : p.Prime) (hR : (p : R) = 0) (n : ℕ) : R →+* R`, and
  `iterateFrobeniusOfPrime_apply`. This recorded repaired interface allows zero rings.
- Proof import `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, a closed embedding with surjective
  stalk maps; the affine reduction quotient description is already available.

Edge cases checked before drafting:

- Empty scheme: Noetherian still holds; the characteristic condition is vacuous,
  every open section ring is zero, a positive `e` exists, and the pointwise
  condition is vacuous. No `Nonempty X` is assumed.
- Empty open inside a nonempty scheme: `→+*` allows zero source and target;
  no `ExpChar` or `Nontrivial` assumption excludes this case.
- Reduced `X`: nilradical is zero, so a positive Frobenius power itself gives
  the required map; the conclusion does not require nilpotents to be present.
- Nonreduced thickening such as `F_p[t]/(t^m)`: `e` must be sufficiently large,
  and is existential, not fixed to one. The uniform bound comes from
  Noetherian compactness; no bound depending on the open is substituted.
- Nonaffine opens and intersections: no global lifting surjectivity is claimed;
  restrictions are quantified for every inclusion, and the proof uses local lifts.
- `p = 2` is included; `p = 0,1` are excluded exactly by primality. The exponent
  is positive; no `e = 0` case has been silently substituted.

Searches (all through the prescribed wrapper, plus read-only local `rg`):

- LeanFinder: `A uniform power of Frobenius gives a ring sheaf morphism from
  the reduction of a Noetherian scheme`. Eight hits: `PerfectionMap.map`,
  `AlgHom.IsArithFrobAt.mk_apply`, `IsPurelyInseparable.iterateFrobeniusₛₗ`,
  `PerfectClosure.iterate_frobenius_mk`, `iterateFrobeniusEquiv_def`,
  `iterateFrobeniusEquiv_apply`, `PerfectRing.liftAux_apply`, and
  `iterateFrobeniusEquiv_eq_pow`; none states the sheaf norm and all its clauses.
- Loogle: `"frobenius", "nilradical"`. One hit,
  `pNilradical_eq_bot_of_frobenius_inj`; a ring reducedness result, not this statement.
- Mathlib grep: `frobenius|Frobenius`, subdirectory `AlgebraicGeometry`:
  zero hits.
- LeanSearch: `A power of Frobenius gives a norm for the reduction of a
  Noetherian scheme in characteristic p`. Eight ring-level Frobenius hits
  (`LinearMap.frobenius`, `iterateFrobenius_mul_apply`, `iterateFrobenius`,
  `iterateFrobeniusEquiv_eq_pow`, `iterate_frobenius`,
  `LinearMap.iterateFrobenius`, `iterateFrobenius_inj`, `iterateFrobenius_def`);
  none is the required reduction sheaf-norm theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and proposed
  declaration: only the consumer `ExistsAmpleOfReductionCharP.lean` cites the
  item in its proof docstring; no existing declaration of this theorem.
- `rg` for Frobenius/nilradical and reduction/norm in project geometry modules:
  `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius` supplies an absolute
  Frobenius and `exists_nilradical_le_ker_iterateFrobenius`, but does not state
  the compatible family with affine and residue-vanishing clauses. The norm
  and ampleness consumers likewise do not give this theorem.

No node fault or STATEMENT-DISPUTED issue was found. The old CompactObject
example and its node were read: that module is currently withdrawn, so its
obsolete declaration was not used. The active module-mode conventions of the
stage brief were followed. All variables/universes are explicit with
`set_option autoImplicit false`; there is no private notation, local instance,
auxiliary definition, or hidden proof in a signature.

## Second reading by NS

A second pass in this worker reread the node, source, complete signature, and
recorded dependency signatures; no second agent was started, as the dispatch
brief explicitly forbids it. This is a self-review, not a claim of independent
review; the maintainer's independent review remains the delivery review.

The pass matched the prime and stalk characteristic assumptions literally,
checked the finite-cover/Noetherian equivalence, and checked the quantifier
order (one positive exponent, one family, all opens). It checked the orientation
of each restriction against `V ≤ W`, the canonical reduction comorphism, the
inverse direction of `subschemeObjIso`, and the use of the quotient of the
actual affine section ring by its nilradical. The final clause uses residue
fields on both schemes, not merely vanishing germs. No clause of the node was
omitted or strengthened, and no mismatch required a statement change. The
module was placed under AlgebraicGeometry rather than SixFunctors because this
is a general scheme-theoretic statement. Direct public statement-dependency
imports and plain proof-dependency imports were checked.

Validation: `scompile.py NS lem-sfb-reduction-frobenius-sheaf-norm` compiled the
statement in module mode against the published server library. Final dry-run
and push results are recorded below after they complete.

Final validation: the final AlgebraicGeometry module passed both server compile
modes (1.5 seconds each), with no errors or unexpected warnings. The prescribed
`deliver2.py ... --no-push` printed `OK (dry run)` for commit `afb42126fe8`:
preflight passed and the delivery compiled. The subsequent delivery repeats the
required checks before pushing.
