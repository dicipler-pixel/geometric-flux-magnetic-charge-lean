# What bends: the options, tested (Jeromie Beasley, 23 Nov 2026, AI-assisted)

Question: is it the infinite covariance of the primes that bends. Scripts PRIME-COVARIANCE-01, WHAT-BENDS-01, WHAT-BENDS-01b; kill lines written before each run.

| Option | Test | Result |
|---|---|---|
| Adding against multiplying (pair covariance) | prime pairs at gaps 2 to 2310 below 5e7, against the product over primes dividing the gap | not flat: 1 to 3.56 times the twin count; prediction matched to 0.25% (the prediction is the Hardy-Littlewood conjecture) |
| End-digit record of the twin chain | nine transitions between end digits 1, 7, 9 of consecutive twin starts, 239,099 pairs | not flat: the same digit twice in a row is 8 to 9% rarer than independent draws; noise 0.6% |
| Zeros push apart | first 400 zeros, share of small neighbouring gaps | 1.0% (26% if free, about 3% if they push) |
| The ball as reader of the chain | real chain against shuffled chains, 600 / 2400 / 9600 pairs | whole steps shuffled: real ends at or just below the low edge (the big early steps coming first); arms only shuffled: inside every time. The ball's end distance does not show the end-digit covariance: failed this way |
| The flat reader (tetrahedron) | derived | steps on one arm add in any order, so it cannot see order at all |

Not run: the two books on elliptic-curve primes (connection-energy paper); curvature on the projector bundle from a prime operator (no operator fixed).
Prior art: Hardy and Littlewood (pairs), Montgomery (zeros), Lemke Oliver and Soundararajan (end digits of consecutive primes).
