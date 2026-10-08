+++
id = "lem-sc-image-subgroup"
kind = "lemma"
title = "The image of a homomorphism is a closed subgroup scheme"
order = 554
uses = ["def-sc-group-scheme", "def-sc-group-scheme-subgroup"]
+++
Let $f:G\to H$ be a homomorphism of
group schemes over a field $k$, with $G$ proper over $k$ and
$H$ separated and of finite type over $k$. Let $Z\subseteq H$ be
the scheme-theoretic image of $f$, i.e. the closed subscheme defined
by the kernel of $\mathcal O_H\to f_*\mathcal O_G$. Then $Z$ is of
finite type over $k$, the induced morphism $f':G\to Z$ is
surjective, and $Z$ is a closed
subgroup scheme of $H$.

## Proof

Being a closed subscheme of the finite type $k$-scheme $H$, $Z$ is
of finite type over $k$. The morphism $f':G\to Z$ is dominant by
construction of the scheme-theoretic image, and it is proper because
$G$ is proper over $k$ and $Z$, a closed subscheme of the
separated $k$-scheme $H$, is separated; a proper dominant morphism
is surjective. Write $j:Z\hookrightarrow H$ for the closed immersion
and $\mathcal I\subseteq\mathcal O_H$ for the ideal of $Z$, so that
$f^*\mathcal I=0$ because $f=j\circ f'$.

*Multiplication.* The morphism
$m_H\circ(j\times j):Z\times_kZ\to H$ satisfies

$$
(m_H\circ(j\times j))\circ(f'\times f')
=m_H\circ(f\times f)=f\circ m_G=j\circ(f'\circ m_G),
$$

using that $f$ is a homomorphism and that $m_H\circ(f\times f)= f\circ m_G$. Pulling the ideal $\mathcal I$ back along
$m_H\circ(j\times j)$ gives
$0$, since the composite with $f'\times f'$ factors through $j$
and $f'\times f'$ is surjective: the support of the pulled-back ideal
is the inverse image of $\operatorname{Supp}\mathcal I$, which is
empty. Hence $m_H\circ(j\times j)$ factors through the closed
subscheme $Z$, i.e. there is $m_Z:Z\times_kZ\to Z$ with
$j\circ m_Z=m_H\circ(j\times j)$. The same argument with $i_H$ in
place of $m_H$ gives $i_Z:Z\to Z$ with $j\circ i_Z=i_H\circ j$,
and $e_H=j\circ(f'\circ e_G)$ factors through $Z$, giving
$e_Z:\Spec k\to Z$ with $j\circ e_Z=e_H$.

*Group axioms.* The associativity, unit and inverse axioms for
$(m_Z,i_Z,e_Z)$ hold after composing with the monomorphism $j$ (they
are the corresponding axioms for $H$, and $j\circ m_Z= m_H\circ(j\times j)$), hence hold on $Z$. Therefore $Z$ is a group
scheme over $k$ in the sense of [def-sc-group-scheme] and $j$
is a homomorphism of group schemes, so $Z$ is a closed
subgroup scheme of $H$,
i.e. a subgroup scheme of $H$ in the sense of
[def-sc-group-scheme-subgroup].
