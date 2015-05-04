# Abomonation
A mortifying serialization library for Rust

Abomonation (spelling intentional) is a serialization library for Rust based on the very simple idea that if someone presents data for serialization it will copy those exact bits, and then follow any pointers and copy those bits. When deserializing it recovers the exact bits, and then corrects pointers to aim at the serialized forms of the chased data.
