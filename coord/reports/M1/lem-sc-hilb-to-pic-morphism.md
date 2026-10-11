## Worker report

Module: `Sheaf.AlgebraicGeometry.HilbertToPicardMorphism`.
Declaration: `AlgebraicGeometry.exists_hilbertToPicardMorphism`.
This is a statement only, with one `sorry`; no definitions or proofs are added.
Source checked online: https://stacks.math.columbia.edu/tag/0BA0, clause (4) and proof paragraph 2, and https://stacks.math.columbia.edu/tag/0B9J. The local literature checkout does not contain pic.tex.

Hypotheses and clauses, with the node and source open:

- A separably closed field: `{k : Type u} [Field k] [IsSepClosed k]`.
- The smooth projective curve and its structure map: `{C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [f.IsSmoothProjectiveCurve]`. This recorded class includes integrality, separatedness, finite type and dimension one, as well as smoothness and projectivity. `[GeometricallyIntegral f]` renders geometric integrality.
- The introductory name g is unused in every conclusion, so no free genus parameter or additional genus hypothesis is introduced. Its definition remains the dependency's `Scheme.arithmeticGenus`; no genus notion is redefined.
- Nonnegative d: `(d : ℕ)`, with `(d : ℤ)` in degree equalities. This parametrizes exactly the nonnegative integers, including zero.
- `H P : Over (Spec (.of k))` are the two arbitrary representing k-schemes; `eH : (hilbertPresheaf f d).RepresentableBy H` is the Hilbert representation.
- The node introduces Pic^d locally as the subfunctor whose sections have identically degree d. The binder `Q : Subfunctor (picardFunctor f).obj` and `hQ : ∀ T c, c ∈ Q.obj (op T) ↔ ∀ t, picardDegree f c t = (d : ℤ)` specify exactly that subfunctor, on every test scheme and every section. This is a presentation of the locally introduced object, not an additional geometric assumption, nor an unconstrained replacement for Pic^d. `eP : Q.toFunctor.RepresentableBy P` supplies precisely its representation. No separate definition of the degree component is made. In particular we do not silently replace this subfunctor by the source's differently packaged sheafification `picardFunctorDegree`.
- The universal closed subscheme is `let D := (eH.homEquiv (𝟙 H)).1`. The subtype property already supplies that D is a Hilbert subscheme, finite locally free of degree d. The product is in the convention C ×_k H, canonically the product H ×_k C of the statement.
- Clause 1 is `D.IsRelativeEffectiveCartier (pullback.snd f H.hom)`. `D.toModulesᵛ.IsInvertible` explicitly gives invertibility of the actual associated dual-ideal module O(D), using the required `Scheme.Modules.IsInvertible` predicate.
- The existential `L : (pullback f H.hom).Pic` is pinned to O(D) by `Nonempty ((fromSkeleton _).obj L.val ≅ D.toModulesᵛ)`. This is its isomorphism class, not an arbitrary line bundle.
- Clause 2's fibrewise degree assertion is `∀ t : H.left, picardPresheafDegree f L t = (d : ℤ)`.
- `c : Q.toFunctor.obj (op H)` is the degree-d class and `c.val = (toPicardFunctor f).app (op H) L` identifies it with the actual sheafification image of O(D). `γ : H ⟶ P` is a k-morphism, and `eP.homEquiv γ = c` says exactly that it corresponds to this class. Existentially presenting these uniquely specified objects avoids definitions depending on postponed proofs.
- Clause 3 quantifies over every `K : Type u` with `[Field K] [Algebra k K]`, and every k-point `x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ H`.
- `DK := (eH.homEquiv x).1` is precisely the corresponding closed subscheme of C_K. Its finite locally free degree d condition is again in its Hilbert subtype property. `DK.IsInvertible` explicitly asserts it is an effective Cartier divisor; `DK.toModulesᵛ.IsInvertible` asserts that O(DK) is invertible.
- `LK` is identified by an isomorphism with that actual dual ideal. `(eP.homEquiv (x ≫ γ)).val = (toPicardFunctor f).app (op T) LK` says that γ composed with x corresponds to the class of O(DK). The left hand side is already a section of Q, so this asserts equality in Pic^d as well as in Pic. Lean's composition order `x ≫ γ` is the node's γ ∘ x.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`: `Scheme.Hom.IsSmoothProjectiveCurve`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral` (the integral alternative in def-pc-geometrically-irreducible's recorded match).
- `WeilConjectures.AlgebraicGeometry.Picard.Defs`: `picardFunctor`, `toPicardFunctor`, `picardPresheaf`.
- `WeilConjectures.AlgebraicGeometry.Picard.Degree`: `picardPresheafDegree`, `picardDegree`. The already recorded node `def-pd-degree-morphism` is added to stmt_deps because the exact membership condition uses its existing declaration; it was already in proof_deps.
- `Mathlib.CategoryTheory.Yoneda`: `Functor.RepresentableBy`, with natural `homEquiv : (T ⟶ H) ≃ F.obj (op T)`.
- `WeilConjectures.AlgebraicGeometry.Hilbert.Defs`: `hilbertPresheaf`, `IsHilbertSubscheme`.
- `WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier`: `Scheme.IdealSheafData.IsRelativeEffectiveCartier`.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`: dual ideal `J.toModulesᵛ`, `IdealSheafData.IsInvertible`, and `IdealSheafData.IsInvertible.isInvertible_dual_toModules`, which is the divisor-line-bundle dependency's recorded declaration. No duplicate divisor definition is added. The effective-Cartier dependency's recorded theorem `isInvertible_toModules` uses the same ideal predicate; its recorded finiteness theorem is a consequence, not a second definition we need to call in a statement.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`: `Scheme.Hom.IsFiniteLocallyFreeOfDegree`. For Hilbert elements these properties are already encoded by `IsHilbertSubscheme`, not assumed again as extra hypotheses.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, field extensions `[Field K] [Algebra k K]`.
- Base change uses `Limits.pullback`, `pullback.snd`, in exactly the convention recorded by `Sheaf.AlgebraicGeometry.BaseChangeConventions`. No module pullback operation is redefined or required by this statement.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: `Scheme.arithmeticGenus`, read but not used because g occurs in no conclusion.

Edge cases checked before writing: d=0 is included (empty divisor, ideal O, dual O, degree zero). The empty test scheme is included in hQ, where degree constancy is vacuous, as it must be. No rational point on C, normalization section, positivity d>0, inequality d≥g, characteristic restriction, or algebraic closedness of k is added. Field extensions need not be finite or algebraic. All scheme/test-field universes are the common u, so residue fields of every test scheme are included; there is no smaller independent test-field universe. All variables and universes are explicitly bound. The representations are arbitrary choices, and no surjectivity or smoothness conclusion for γ is added.

Searches made:

- msearch.py LeanSearch: `Hilbert scheme divisors morphism to Picard scheme`. Service returned Internal Server Error; recorded unavailable, no mathematical verdict drawn.
- msearch.py LeanFinder, same query: eight unrelated affine/projective-space construction hits; no matching statement.
- msearch.py Loogle: `AlgebraicGeometry.Scheme, CategoryTheory.Functor.RepresentableBy`: `Scheme.LocalRepresentability.representableBy`, general Zariski representability, not this morphism.
- msearch.py grep: `hilbert.*picard|picard.*hilbert` in Mathlib/AlgebraicGeometry: zero hits.
- rg of WeilConjectures and lean/Sheaf for `exists_hilbertToPicardMorphism|hilbert.*[Pp]icard|[Pp]icard.*hilbert`: no matching declaration (one incidental Hilbert-90 comment in PicardLift).
- rg for the exact node id in WeilConjectures: no hits. Search of dag/lean_names_upstream.json for the Hilbert-to-Picard names: no matching declaration.
- Read Picard/Jacobian.lean's `picardSubfunctorDegree`, `picardFunctorDegree` and `mem_picardSubfunctorDegree_iff`: existing constructions but no theorem carrying this node's three conclusions. These are a degree subfunctor of the Picard presheaf and its sheafification; the node instead specifies the subfunctor of the Picard functor. The constrained Q binder renders the latter directly with Mathlib Subfunctor.

No statement correction, new node or dependency replacement was necessary. No STATEMENT-DISPUTED issue found.

Validation: scompile.py server compilation returned exit code 0, compiled in 2.1 seconds, with no warnings. Delivery dry run is the final verification; the independent second reading is left to the designated reader.


## Second reading by M1

Independent review of the node copy, its unchanged base statement and seven proof steps,
all statement-dependency node records, and the delivered Lean. Verdict: faithful statement;
no Lean or node repair required. Only this second-reading report is added.

### Source and standing hypotheses

The local literature checkout has no stacks-project directory. I independently read the
Stacks `pic.tex` source from
https://raw.githubusercontent.com/stacks/stacks-project/master/pic.tex,
labels `lemma-picard-pieces` (0BA0) and `remark-universal-object-hilb-d` (0B9J).
The former assumes a separably closed field and a smooth projective curve of genus g;
clause (4) and proof paragraph two construct gamma from the universal divisor by Yoneda.
Its degree component is specified by fibre Euler characteristic d+1-g. The latter assumes
a geometrically irreducible smooth proper curve and explains the dual-ideal line bundle
and its restriction to a divisor point. Its displayed d+1 is not an exclusion of degree
zero in 0BA0 (4): the node explicitly handles zero using the Cartier criterion, and the
Lean retains it. A chosen rational section in the source proof is not a hypothesis on the
construction; the Lean does not introduce one.

### Objects, hypotheses, and conclusions matched item by item

1. Base field k, separably closed: `{k : Type u} [Field k] [IsSepClosed k]`.
   PASS: separably closed, not algebraically closed; no characteristic restriction.
2. Curve C over k and its structure map: `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))`
   with `[f.IsSmoothProjectiveCurve]` and `[GeometricallyIntegral f]`.
   PASS: read SmoothProjectiveCurve.lean and its imported Variety.lean. The former
   extends IsCurveOverField, Smooth and IsProjective. The latter requires an integral,
   separated, finite-type scheme of dimension exactly one. Read Mathlib's
   GeometricallyIntegral signature: every field base change is integral. These are the
   node's exact hypotheses, with no extra Noetherian or rational-point instance.
3. Genus g = dim H^1(O_C): this is introductory notation and occurs in none of the
   three conclusions. PASS: no independent g, equality assumption or bound is needed.
   Read Scheme.arithmeticGenus in Cohomology/EulerChar.lean, the recorded definition;
   no second genus notion is introduced.
4. Integer degree d >= 0: `(d : ℕ)` and `(d : ℤ)` in degree equalities.
   PASS: this is exactly the nonnegative integer range, including zero. The preliminary
   definition of Pic^d for arbitrary integer d does not assert an additional conclusion
   for negative degrees.
5. Degree component Pic^d of Pic_{C/k}: `(Q : Subfunctor (picardFunctor f).obj)` and
   `hQ : ∀ T c, c ∈ Q.obj (op T) ↔ ∀ t : T.left, picardDegree f c t = (d : ℤ)`.
   PASS: every test k-scheme and every section is quantified. hQ fixes exactly the
   carrier of the node's locally introduced subfunctor, not an extra geometric
   hypothesis. Read picardFunctor and toPicardFunctor in Picard/Defs.lean: fppf
   sheafification and its unit. Read picardDegree in Picard/Degree.lean: the degree of
   local representatives, with picardDegree_toPicardFunctor identifying it with
   fibrewise degree. The already landed def-pd-degree-morphism addition to stmt_deps
   is justified by this use; it was already in proof_deps.
6. Arbitrary representing schemes H_d and P_d: `(H P : Over (Spec (.of k)))`,
   `(eH : (hilbertPresheaf f d).RepresentableBy H)` and
   `(eP : Q.toFunctor.RepresentableBy P)`.
   PASS: read Mathlib RepresentableBy, whose homEquiv is a natural bijection from
   morphisms into the representing object to sections. Over gives actual k-morphisms.
   There is no assumption that either representation is a particular chosen scheme.
7. Universal closed subscheme D_d: `let D := (eH.homEquiv (𝟙 H)).1`.
   PASS: read hilbertPresheaf and IsHilbertSubscheme in Hilbert/Defs.lean: sections are
   quasi-coherent ideals on pullback f T.hom with finite, flat, locally finitely
   presented subscheme projection of rank d. Thus the subtype already supplies all
   finiteness and degree conditions. C ×_k H is canonically H ×_k C. Read the
   BaseChangeConventions dependency: pullback.snd is the structure map to H.
8. Conclusion (1), relative effective Cartier and actual O(D_d):
   `D.IsRelativeEffectiveCartier (pullback.snd f H.hom)` and
   `D.toModulesᵛ.IsInvertible`.
   PASS: read IsRelativeEffectiveCartier = invertible ideal plus flat subscheme
   projection. Read the imported ideal IsInvertible predicate: locally regular
   principal ideals, exactly effective Cartier, not merely module invertibility.
   Read EffectiveCartier.lean's isInvertible_toModules and
   isInvertible_dual_toModules: O(D) is the dual of the ideal module.
9. Conclusion (2), its actual class and fibrewise degree:
   `∃ L : (pullback f H.hom).Pic`,
   `Nonempty ((fromSkeleton _).obj L.val ≅ D.toModulesᵛ)`, and
   `∀ t : H.left, picardPresheafDegree f L t = (d : ℤ)`.
   PASS: the isomorphism pins L to O(D), rather than leaving an arbitrary invertible
   module. Read picardPresheafDegree: Euler characteristic of the fibre representative
   minus that of the fibre structure sheaf, precisely def-pd-fibrewise-degree.
10. Conclusion (2), membership and the corresponding gamma:
    `∃ (c : Q.toFunctor.obj (op H)) (γ : H ⟶ P)`,
    `c.val = (toPicardFunctor f).app (op H) L ∧ eP.homEquiv γ = c`.
    PASS: c is a degree-d section and is the sheafification image of O(D); the
    representing bijection specifies gamma uniquely. Existential presentation avoids
    a definition whose construction would require a postponed proof. It loses no
    canonical identification: c, L and gamma are fixed by the preceding equalities.
11. Conclusion (3), every extension and point:
    `∀ (K : Type u) [Field K] [Algebra k K] (x : Over.mk (Spec.map
    (CommRingCat.ofHom (algebraMap k K))) ⟶ H)` followed by
    `let T := ...; let DK := (eH.homEquiv x).1`.
    PASS: Algebra over fields is the recorded extension notion; the point is over k.
    The Hilbert subtype gives the exact closed subscheme of C_K finite locally free
    of degree d. Extensions need not be algebraic, finite or separably closed.
12. Conclusion (3), effective Cartier and its line bundle's class:
    `DK.IsInvertible ∧ DK.toModulesᵛ.IsInvertible ∧ ∃ LK`,
    `Nonempty ((fromSkeleton _).obj LK.val ≅ DK.toModulesᵛ)` and
    `(eP.homEquiv (x ≫ γ)).val = (toPicardFunctor f).app (op T) LK`.
    PASS: the ideal predicate says DK is effective Cartier; LK is exactly O(DK).
    The displayed equality is in Pic, with the left side already in Q; inclusion
    of a subfunctor is injective, so it states precisely the required equality in
    Pic^d. Lean x ≫ gamma is the node's gamma composed with x. A relative-Cartier
    conclusion for DK is not needed by the node's third clause.

The recorded finite-locally-free dependency was also read in Morphisms/FiberDegree.lean:
its degree is dim over the residue field of global functions on the fibre. The Hilbert
functor's flat finite rank is the same degree; no additional assumption is made in this
statement. All dependency notions are reused. No new definition node or dependency
module is present or needed. There is no statement_change or corrected statement to
review, so the corrected-citer check does not apply.

### Edge cases and hygiene

Degree zero remains included: the empty divisor has unit ideal, whose dual is O,
and degree zero. Empty test schemes remain in hQ; the pointwise condition is correctly
vacuous there. Empty C is already excluded by the node's integral dimension-one curve
hypothesis, not by a new Lean restriction. No index sets or auxiliary n occur.
Arbitrary characteristic is allowed, and every field-valued point in the scheme universe
is included. The common arbitrary universe u can be enlarged to contain any given base,
schemes and extension; no smaller independent test universe makes a hypothesis vacuous.
Picard values live in Type (u+1), as in the imported definition. Every variable and
universe in the declaration is explicitly bound. The existential witnesses occur before
the universal K and x, ensuring a single gamma works for all field-valued points.

One theorem, whose proof is only sorry; no definitions and no proof work added.
The module and theorem docstrings name 0BA0/0B9J and the exact blueprint id; the theorem
follows all seven node proof steps (family geometry, universal Cartier divisor, residue
fibre, degree, Yoneda gamma, field-point divisor, naturality). Namespaces, topic path,
imports and the 100-character line limit match conventions. Checked that lean.statement
is verbatim equal to the file signature, not merely whitespace-equivalent.

### Independent searches and repairs

- LeanSearch through msearch.py: `universal divisor Abel Jacobi morphism Picard degree
  component` returned Internal Server Error, recorded unavailable without a verdict.
- LeanFinder: `universal effective divisor induces Abel map to Picard functor` returned
  eight hits about affine Weierstrass points and class groups, no matching construction.
- Loogle: `"picard"` returned ODE Picard iteration declarations, no algebraic-geometric
  Hilbert-to-Picard statement.
- Independent rg on Mathlib/AlgebraicGeometry using `picard`, `abel.?jacobi` and
  `hilbert scheme` found only incidental elliptic-curve Picard-group comments.
- Independent rg on WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json using
  `abel.?jacobi`, `hilbertToPicard`, `hilb.*picard` and `picard.*hilb` found Hilbert
  representability, incidental comments and Picard representability proofs, not this
  three-clause theorem. Opened Picard/Jacobian.lean's picardSubfunctorDegree,
  picardFunctorDegree and mem_picardSubfunctorDegree_iff: the former is a subfunctor
  of the unsheafified Picard presheaf; the latter is its sheafification. Neither is
  the literal degree subfunctor of picardFunctor fixed by hQ, nor supplies this theorem.
  Thus Q/hQ does not duplicate an existing definition; it specifies the object introduced
  locally by the node with Mathlib Subfunctor and the recorded picardDegree.

No semantic mismatch found. No statement, dependency, signature, or module changed.
The initial compile invocation used a relative sandbox module path from the repository
cwd and failed locally with FileNotFoundError; reran with the absolute sandbox path.

Second-reader validation: remote scompile.py compiled the module in 2.1 seconds,
exit code 0, with no warnings. No unbound variables or universes found by inspection.
