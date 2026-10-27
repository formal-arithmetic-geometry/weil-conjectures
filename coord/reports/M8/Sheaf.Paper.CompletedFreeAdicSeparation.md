## What changed

Marked `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedFree_adicSeparated`
in `Sheaf.Paper.CompletedFreeAdicSeparation` as `STATEMENT-DISPUTED`.
Its signature and its existing hole are unchanged. The claimed assertion is
false for the non-quasi-separated objects that the actual small pro-etale site
allows. This delivery reports the obstruction rather than introducing another
false split-off theorem. No shared definitions or consumer interfaces change.

## Proved and sorry left

Original holes closed: 0 of 1. New holes: 0. Split-off statements: 0.

The original hole remains in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedFree_adicSeparated`
(node `lem-sfb-completed-free-adic-separation`). It cannot correctly be filled
with the present quantification over all representables.

The counterexample below is a mathematical counterexample, not a fully
Lean-formalized scheme construction. Auxiliary scratch checks validate the
power-sequence calculation, its nonvanishing, and independence of two distinct
basis elements. The sheafification nonvanishing criterion is the contrapositive
of `Presheaf.equalizerSieve_mem` for `toSheafify`. These checks do not certify
the entire geometric counterexample. Scratch files are outside `lean/` and are
not delivered as library code.

The flagged item module compiles in 4.2 seconds. A separate Lean check proves
that every compact subset of `OnePoint N` contained either in N or in the
singleton infinity is finite, and that a finite family of such sets cannot
cover `OnePoint N`. Both of these checked declarations use only `propext`,
`Classical.choice`, and `Quot.sound` (1.5-second compile).

## No longer needed

None. No imports, nodes, modules, declarations, or maintainer approvals are
removed. The parent still uses this node, so withdrawal is not authorized by
the counterexample alone. In particular, neither
`Sheaf.Paper.CompletedCoefficientFreeGenerator` nor its consumers are silently
weakened or withdrawn.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: `completedFree_adicSeparated` is false without a restriction
on the representable. The following example satisfies even global divisibility,
which is stronger than the theorem's covering-image-sieve hypotheses.

1. **The base scheme.** Let S be the one-point compactification of the discrete
   space N, with limit point infinity. Let A be the Boolean ring of finite or
   cofinite subsets of N, with symmetric difference and intersection as its
   operations. Equivalently, A is the ring of eventually constant sequences in
   F_2. Its prime spectrum X is S: the principal ultrafilters are the isolated
   natural-number points, and the cofinite ultrafilter is infinity. This is an
   affine scheme. Set E = X minus {infinity}; E is open and is the union of the
   isolated points, but is not quasi-compact. Take the prime l = 3, which is also
   invertible on this characteristic-two base.

2. **The permitted site object.** Glue two copies of X along the common open
   subscheme E, using the identity on E. Write U for the resulting scheme and
   p : U -> X for the map induced by the identity on each copy. It is a local
   isomorphism, hence etale and weakly etale. Therefore it is an object of the
   small site used by the Lean statement. Its two sections s,t : X -> U have
   equalizer exactly E. Their images are affine opens of U with non-quasi-compact
   intersection E, so U is not quasi-separated. No hypothesis in the statement
   excludes it. In Mathlib, `Scheme.ProEt` is
   `MorphismProperty.Over @WeaklyEtale top X`; it imposes no separatedness or
   quasi-separatedness condition.

3. **Sections of the actual coefficient ring.** A constant finite set sheaf on
   this site is represented by the corresponding finite disjoint union of X.
   Consequently, its sections on any site object W are the locally constant
   functions from the underlying space of W to that finite set. Applying this
   to the finite rings Z/3^(k+1), and using that limits of sheaves are computed
   on sections, identifies the ring R(W) in the statement with continuous
   functions |W| -> Z_3. The transitions and projections are the actual residue
   maps defining `purTwistZlCompletion`; no discrete/completed coefficient
   substitution is involved.

4. **The section.** Let a in R(X) be the continuous function with a(n)=3^n and
   a(infinity)=0. Continuity at infinity follows from 3^n -> 0 in Z_3. Let Q be
   the free R-presheaf on the representable U, and let eta be its module
   sheafification unit. In Q(X), set

       z = a ([s] - [t]),       x = eta_X(z).

   The universe lift of the representable merely replaces s,t by their ULifts;
   it changes neither this construction nor equality of basis elements.

5. **Divisibility by every power.** For every positive m, define a continuous
   coefficient b_m by b_m(infinity)=0, b_m(n)=0 for n<m, and
   b_m(n)=3^(n-m) for n>=m. Put d_m=a-3^m b_m. This coefficient is supported
   on the finite clopen subset D_m={0,...,m-1} of E. The section
   d_m([s]-[t]) is zero after sheafification: on D_m the two maps s,t agree,
   and on its open complement d_m=0. These two opens form a Zariski covering,
   hence a pro-etale covering. Thus

       x = 3^m eta_X(b_m([s]-[t])).

   With m=n+1 this is precisely a global witness for each multiplication map
   in the theorem. Each image sieve contains the identity and is therefore top.

6. **Nonvanishing.** For a site morphism f : W -> X, the restriction of z in
   the free presheaf is zero exactly when either s f = t f or a|W = 0. Indeed,
   two distinct basis elements of a free module have independent coefficients.
   The first alternative is equivalent to f factoring through E, because E is
   the equalizer of s,t. The second is equivalent to |f| having image contained
   in {infinity}: all values a(n)=3^n are nonzero in Z_3, and section rings are
   the continuous-function rings of step 3. Thus the zero sieve of z consists
   exactly of morphisms whose images are contained in E or in {infinity}.

   This sieve is not covering. On the quasi-compact target X, a pro-etale cover
   must cover X by the images of finitely many quasi-compact opens of its
   source objects. This is the actual qc-cover condition in
   `Scheme.proetalePrecoverage`, not an assumption that all site objects or all
   covering families are finite. The continuous image of each such
   quasi-compact open is compact in the Hausdorff space S. If it is contained
   in E, it is a compact subset of a discrete space and hence finite. If it is
   contained in {infinity}, it contributes at most infinity. Finitely many such
   images cannot cover the infinitely many natural-number points of S.
   The same conclusion holds for covering sieves, since this precoverage has
   identities and is stable under base change and composition.

   Finally, the sheafification unit is locally injective. If x=eta_X(z) were
   zero, the equalizer sieve of z and zero would therefore be covering,
   contradicting the preceding paragraph. Hence x is nonzero.

The error is in the second step of the node's proposed proof, which asserts
the existence of one covering refinement carrying all equalities in the free
presheaf. Repleteness concerns inverse sequences of **sheaves** with epimorphic
transition maps. It does not say that a countable intersection of arbitrary
covering sieves covers, or that infinitely many equalities in sheafifications
can simultaneously be lifted to equalities in the original presheaf. In this
example the zero sieves of the finite reductions are all covering, while their
intersection is exactly the non-covering sieve described above. Grouping a
fixed finite support does not repair this failure: the support already has
only two generators.

The blueprint coefficient paragraph cited by the original node does not
state this arbitrary-representable separation assertion. Its introduction was
an additional proof-route choice. A possible future repair is to use suitably
restricted generators and then descend the section-action identity from a
cover; that requires checking and adapting the parent argument. This delivery
does not assume that adding a separatedness hypothesis is sufficient, and
does not replace the present assertion with a weaker one.

Relevant source checks: Mathlib
`AlgebraicGeometry/Sites/Proetale.lean` (the category and precoverage),
`AlgebraicGeometry/Cover/QuasiCompact.lean` (the finite compact-image covering
condition), and `CategoryTheory/Sites/LocallyBijective.lean` and
`LocallyInjective.lean` (local injectivity of `toSheafify` and
`Presheaf.equalizerSieve_mem`). Searches through msearch used leanfinder,
Loogle, and grep; none supplied the claimed separation statement.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
